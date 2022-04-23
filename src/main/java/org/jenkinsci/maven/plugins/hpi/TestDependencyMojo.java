package org.jenkinsci.maven.plugins.hpi;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.apache.maven.RepositoryUtils;
import org.apache.maven.artifact.Artifact;
import org.apache.maven.artifact.DefaultArtifact;
import org.apache.maven.artifact.resolver.filter.ArtifactFilter;
import org.apache.maven.artifact.versioning.ArtifactVersion;
import org.apache.maven.artifact.versioning.ComparableVersion;
import org.apache.maven.artifact.versioning.DefaultArtifactVersion;
import org.apache.maven.artifact.versioning.OverConstrainedVersionException;
import org.apache.maven.artifact.versioning.VersionRange;
import org.apache.maven.execution.MavenSession;
import org.apache.maven.lifecycle.internal.LifecycleDependencyResolver;
import org.apache.maven.model.Dependency;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugin.MojoFailureException;
import org.apache.maven.plugin.logging.Log;
import org.apache.maven.plugins.annotations.Component;
import org.apache.maven.plugins.annotations.Mojo;
import org.apache.maven.plugins.annotations.Parameter;
import org.apache.maven.plugins.annotations.ResolutionScope;
import org.apache.maven.project.DefaultDependencyResolutionRequest;
import org.apache.maven.project.DefaultProjectBuildingRequest;
import org.apache.maven.project.DependencyResolutionException;
import org.apache.maven.project.DependencyResolutionRequest;
import org.apache.maven.project.DependencyResolutionResult;
import org.apache.maven.project.MavenProject;
import org.apache.maven.project.ProjectBuildingRequest;
import org.apache.maven.project.ProjectDependenciesResolver;
import org.apache.maven.shared.dependency.graph.DependencyCollectorBuilder;
import org.apache.maven.shared.dependency.graph.DependencyCollectorBuilderException;
import org.apache.maven.shared.dependency.graph.DependencyNode;
import org.apache.maven.shared.dependency.graph.traversal.DependencyNodeVisitor;
import org.apache.maven.shared.transfer.artifact.resolve.ArtifactResolverException;

/**
 * Places test-dependency plugins into somewhere the test harness can pick up.
 *
 * <p>
 * See {@code TestPluginManager.loadBundledPlugins()} where the test harness uses it.
 *
 * <p>Additionally, it may adjust the classpath for {@code surefire:test} to run tests
 * against different versions of various dependencies than what was configured in the POM.
 */
@Mojo(name="resolve-test-dependencies", requiresDependencyResolution = ResolutionScope.TEST)
public class TestDependencyMojo extends AbstractHpiMojo {

    @Component
    private DependencyCollectorBuilder dependencyCollectorBuilder;

    /**
     * List of dependency version overrides in the form {@code groupId:artifactId:version} to apply during testing.
     * Must correspond to dependencies already present in the project model.
     */
    @Parameter(property = "overrideVersions")
    private List<String> overrideVersions;

    /**
     * Whether to update all transitive dependencies to the upper bounds. Effectively causes same
     * behavior as the {@code requireUpperBoundDeps} Enforcer rule would, if the specified
     * dependencies were to be written to the POM. Intended for use in conjunction with {@link
     * #overrideVersions}.
     */
    @Parameter(property = "useUpperBounds")
    private boolean useUpperBounds;

    @Inject private ProjectDependenciesResolver dependenciesResolver;

    @Override
    public void execute() throws MojoExecutionException, MojoFailureException {
        Map<String, String> overrides = new HashMap<>(); // groupId:artifactId → version
        if (overrideVersions != null) {
            for (String override : overrideVersions) {
                Matcher m = Pattern.compile("([^:]+:[^:]+):([^:]+)").matcher(override);
                if (!m.matches()) {
                    throw new MojoExecutionException("illegal override: " + override);
                }
                overrides.put(m.group(1), m.group(2));
            }
        }

        if (!overrides.isEmpty()) {
            // Create a shadow project for dependency analysis.
            MavenProject shadow = project.clone();

            // First pass: apply the overrides specified by the user.
            pass(overrides, shadow, getLog());

            if (useUpperBounds) {
                // Do upper bounds analysis.
                DependencyNode node;
                try {
                    ProjectBuildingRequest buildingRequest =
                            new DefaultProjectBuildingRequest(session.getProjectBuildingRequest());
                    buildingRequest.setProject(shadow);
                    ArtifactFilter filter = null; // we need to evaluate all scopes;
                    node = dependencyCollectorBuilder.collectDependencyGraph(buildingRequest, filter);
                } catch (DependencyCollectorBuilderException x) {
                    throw new MojoExecutionException("could not analyze dependency tree for useUpperBounds: " + x, x);
                }
                RequireUpperBoundDepsVisitor visitor = new RequireUpperBoundDepsVisitor();
                node.accept(visitor);
                Map<String, String> upperBounds = visitor.upperBounds();

                for (String dep : upperBounds.keySet()) {
                    if (overrides.containsKey(dep)) {
                        throw new AssertionError("overrides should not contain dependency " + dep + " that was inferred by upper bounds");
                    }
                }

                // Second pass: apply the results of the upper bounds analysis.
                pass(upperBounds, shadow, getLog());
                overrides.putAll(upperBounds);
            }

            Map<String, String> preResolve = new HashMap<>();
            for (Artifact artifact : shadow.getArtifacts()) {
                preResolve.put(toKey(artifact), artifact.getVersion());
            }
            shadow.setDependencyArtifacts(null); // force re-resolution
            Set<Artifact> resolved = resolveDependencies(shadow);
            Map<String, String> postResolve = new HashMap<>();
            for (Artifact artifact : resolved) {
                postResolve.put(toKey(artifact), artifact.getVersion());
            }
            for (Map.Entry<String, String> entry : postResolve.entrySet()) {
                String preVersion = preResolve.get(entry.getKey());
                String postVersion = entry.getValue();
                if (!preVersion.equals(postVersion)) {
                    if (new ComparableVersion(preVersion).compareTo(new ComparableVersion(postVersion)) > 0) {
                        throw new AssertionError("this should never happen");
                    }
                    overrides.put(entry.getKey(), postVersion);
                    getLog().debug("after re-resolving, adjusting " + entry.getKey() + " to " + postVersion);
                }
            }
        }

        File testDir = new File(project.getBuild().getTestOutputDirectory(), "test-dependencies");
        try {
            Files.createDirectories(testDir.toPath());
        } catch (IOException e) {
            throw new MojoExecutionException("Failed to create directories for '" + testDir + "'", e);
        }

        try (FileOutputStream fos = new FileOutputStream(new File(testDir, "index")); Writer w = new OutputStreamWriter(fos, StandardCharsets.UTF_8)) {
            for (MavenArtifact a : getProjectArtfacts()) {
                if (!a.isPluginBestEffort(getLog()))
                    continue;

                String artifactId = a.getActualArtifactId();
                if (artifactId == null) {
                    getLog().debug("Skipping " + artifactId + " with classifier " + a.getClassifier());
                    continue;
                }

                getLog().debug("Copying " + artifactId + " as a test dependency");
                File dst = new File(testDir, artifactId + ".hpi");
                File src;
                String version = overrides.get(a.getGroupId() + ":" + artifactId);
                if (version != null) {
                    src = replace(a.getHpi().artifact, version).getFile();
                } else {
                    src = a.getHpi().getFile();
                }
                FileUtils.copyFile(src, dst);
                w.write(artifactId + "\n");
            }
        } catch (IOException e) {
            throw new MojoExecutionException("Failed to copy dependency plugins",e);
        }

        if (!overrides.isEmpty()) {
            List<String> additionalClasspathElements = new ArrayList<>();
            List<String> classpathDependencyExcludes = new ArrayList<>();
            for (Map.Entry<String, String> entry : overrides.entrySet()) {
                String key = entry.getKey();
                classpathDependencyExcludes.add(key);
                String[] groupArt = key.split(":");
                String groupId = groupArt[0];
                String artifactId = groupArt[1];
                String version = entry.getValue();
                // Cannot use MavenProject.getArtifactMap since we may have multiple dependencies of different classifiers.
                boolean found = false;
                for (Artifact a : project.getArtifacts()) {
                    if (!a.getGroupId().equals(groupId) || !a.getArtifactId().equals(artifactId)) {
                        continue;
                    }
                    found = true;
                    if (a.getArtifactHandler().isAddedToClasspath()) { // everything is added to test CP, so no need to check scope
                        additionalClasspathElements.add(replace(a, version).getFile().getAbsolutePath());
                    }
                }
                if (!found) {
                    throw new MojoExecutionException("could not find dependency " + key);
                }
            }
            Properties properties = project.getProperties();
            getLog().info("Replacing POM-defined classpath elements " + classpathDependencyExcludes + " with " + additionalClasspathElements);
            // cf. http://maven.apache.org/surefire/maven-surefire-plugin/test-mojo.html
            properties.setProperty("maven.test.additionalClasspath", String.join(",", additionalClasspathElements));
            properties.setProperty("maven.test.dependency.excludes", String.join(",", classpathDependencyExcludes));
        }
    }

    private static void pass(Map<String, String> overrides, MavenProject project, Log log)
            throws MojoFailureException {
        Set<String> updatedDependencies = new HashSet<>();

        // Update existing dependency entries in the model
        for (Dependency dependency : project.getDependencies()) {
            if (updateDependency(overrides, dependency, log)) {
                updatedDependencies.add(toKey(dependency));
            }
        }

        // Update existing dependency management entries in the model
        if (project.getDependencyManagement() != null) {
            for (Dependency dependency : project.getDependencyManagement().getDependencies()) {
                if (updateDependency(overrides, dependency, log)) {
                    updatedDependencies.add(toKey(dependency));
                }
            }
        }

        // If an override was requested for a transitive dependency that is not in the model, add a
        // dependency management entry
        Set<String> unappliedDependencies = new HashSet<>(overrides.keySet());
        unappliedDependencies.removeAll(updatedDependencies);
        for (Artifact artifact : project.getArtifacts()) {
            String key = toKey(artifact);
            if (unappliedDependencies.contains(key)) {
                Dependency dependency = new Dependency();
                dependency.setArtifactId(artifact.getArtifactId());
                dependency.setGroupId(artifact.getGroupId());
                dependency.setVersion(overrides.get(key));
                dependency.setScope(artifact.getScope());
                dependency.setType(artifact.getType());
                dependency.setClassifier(artifact.getClassifier());
                // TODO what if dependency management is null?
                project.getDependencyManagement().addDependency(dependency);
                updatedDependencies.add(key);
            }
        }
        unappliedDependencies.removeAll(updatedDependencies);
        if (!unappliedDependencies.isEmpty()) {
            throw new MojoFailureException("could not find dependencies " + unappliedDependencies);
        }
        log.debug("adjusted dependencies: " + project.getDependencies());
        if (project.getDependencyManagement() != null) {
            log.debug("adjusted dependency management: " + project.getDependencyManagement().getDependencies());
        }

        // Now update the artifacts corresponding to the model changes
        Set<String> updatedArtifacts = new HashSet<>();
        for (Artifact artifact : project.getArtifacts()) {
            String key = toKey(artifact);
            if (updatedDependencies.contains(key)) {
                String overrideVersion = overrides.get(key);
                if (overrideVersion != null) {
                    artifact.setVersion(overrideVersion);
                    updatedArtifacts.add(key);
                }
            }
        }
        Set<String> unappliedArtifacts = new HashSet<>(overrides.keySet());
        unappliedArtifacts.removeAll(updatedArtifacts);
        if (!unappliedArtifacts.isEmpty()) {
            throw new MojoFailureException("could not find artifacts " + unappliedArtifacts);
        }
    }

    private static boolean updateDependency(
            Map<String, String> overrides, Dependency dependency, Log log) {
        String key = toKey(dependency);
        String overrideVersion = overrides.get(key);
        if (overrideVersion != null) {
            log.debug("For dependency analysis, updating " + key + " from " + dependency.getVersion() + " to " + overrideVersion);
            dependency.setVersion(overrideVersion);
            return true;
        }
        return false;
    }

    /**
     * Performs the equivalent of the "@requiresDependencyResolution" mojo attribute.
     *
     * @see LifecycleDependencyResolver#getDependencies(MavenProject, Collection, Collection,
     *     MavenSession, boolean, Set)
     */
    private Set<Artifact> resolveDependencies(MavenProject project) throws MojoExecutionException {
        try {
            DependencyResolutionRequest request =
                    new DefaultDependencyResolutionRequest(project, session.getRepositorySession());
            DependencyResolutionResult result = dependenciesResolver.resolve(request);

            Set<Artifact> artifacts = new LinkedHashSet<>();
            if (result.getDependencyGraph() != null
                    && !result.getDependencyGraph().getChildren().isEmpty()) {
                RepositoryUtils.toArtifacts(
                        artifacts,
                        result.getDependencyGraph().getChildren(),
                        Collections.singletonList(project.getArtifact().getId()),
                        request.getResolutionFilter());
            }
            return artifacts;
        } catch (DependencyResolutionException e) {
            throw new MojoExecutionException("Unable to copy dependency plugin", e);
        }
    }

    private Artifact replace(Artifact a, String version) throws MojoExecutionException {
        Artifact a2 = new DefaultArtifact(a.getGroupId(), a.getArtifactId(), VersionRange.createFromVersion(version), a.getScope(), a.getType(), a.getClassifier(), a.getArtifactHandler(), a.isOptional());
        try {
            return artifactResolver.resolveArtifact(session.getProjectBuildingRequest(), a2).getArtifact();
        } catch (ArtifactResolverException x) {
            throw new MojoExecutionException("could not find " + a + " in version " + version + ": " + x, x);
        }
    }

    // Adapted from RequireUpperBoundDeps @ 731ea7a693a0986f2054b6a73a86a31373df59ec. TODO delete extraneous stuff and simplify to the logic we actually need here:
    private class RequireUpperBoundDepsVisitor implements DependencyNodeVisitor {

        private boolean uniqueVersions;

        public void setUniqueVersions(boolean uniqueVersions) {
            this.uniqueVersions = uniqueVersions;
        }

        private Map<String, List<DependencyNodeHopCountPair>> keyToPairsMap = new LinkedHashMap<>();

        public boolean visit(DependencyNode node) {
            DependencyNodeHopCountPair pair = new DependencyNodeHopCountPair(node);
            String key = pair.constructKey();
            List<DependencyNodeHopCountPair> pairs = keyToPairsMap.get(key);
            if (pairs == null) {
                pairs = new ArrayList<>();
                keyToPairsMap.put(key, pairs);
            }
            pairs.add(pair);
            Collections.sort(pairs);
            return true;
        }

        public boolean endVisit(DependencyNode node) {
            return true;
        }

        // added for TestDependencyMojo in place of getConflicts/containsConflicts
        public Map<String, String> upperBounds() {
            Map<String, String> r = new HashMap<>();
            for (List<DependencyNodeHopCountPair> pairs : keyToPairsMap.values()) {
                DependencyNodeHopCountPair resolvedPair = pairs.get(0);

                // search for artifact with lowest hopCount
                for (DependencyNodeHopCountPair hopPair : pairs.subList(1, pairs.size())) {
                    if (hopPair.getHopCount() < resolvedPair.getHopCount()) {
                        resolvedPair = hopPair;
                    }
                }

                ArtifactVersion resolvedVersion = resolvedPair.extractArtifactVersion(uniqueVersions, false);

                for (DependencyNodeHopCountPair pair : pairs) {
                    ArtifactVersion version = pair.extractArtifactVersion(uniqueVersions, true);
                    if (resolvedVersion.compareTo(version) < 0) {
                        Artifact artifact = resolvedPair.node.getArtifact();
                        if (!artifact.getScope().equals(Artifact.SCOPE_PROVIDED)) {
                            String key = toKey(artifact);
                            getLog().info("for " + key + ", upper bounds forces an upgrade from " + resolvedVersion + " to " + version);
                            r.put(key, version.toString());
                        }
                    }
                }
            }
            return r;
        }

    }

    private static class DependencyNodeHopCountPair implements Comparable<DependencyNodeHopCountPair> {

        private DependencyNode node;

        private int hopCount;

        private DependencyNodeHopCountPair(DependencyNode node) {
            this.node = node;
            countHops();
        }

        private void countHops() {
            hopCount = 0;
            DependencyNode parent = node.getParent();
            while (parent != null) {
                hopCount++;
                parent = parent.getParent();
            }
        }

        private String constructKey() {
            Artifact artifact = node.getArtifact();
            return toKey(artifact);
        }

        public DependencyNode getNode() {
            return node;
        }

        private ArtifactVersion extractArtifactVersion(boolean uniqueVersions, boolean usePremanagedVersion) {
            if (usePremanagedVersion && node.getPremanagedVersion() != null) {
                return new DefaultArtifactVersion(node.getPremanagedVersion());
            }

            Artifact artifact = node.getArtifact();
            String version = uniqueVersions ? artifact.getVersion() : artifact.getBaseVersion();
            if (version != null) {
                return new DefaultArtifactVersion(version);
            }
            try {
                return artifact.getSelectedVersion();
            } catch (OverConstrainedVersionException e) {
                throw new RuntimeException("Version ranges problem with " + node.getArtifact(), e);
            }
        }

        public int getHopCount() {
            return hopCount;
        }

        @SuppressFBWarnings(value = "EQ_COMPARETO_USE_OBJECT_EQUALS", justification = "Silly check; it is perfectly reasonable to implement Comparable by writing a compareTo without an equals.")
        public int compareTo(DependencyNodeHopCountPair other) {
            return Integer.compare(hopCount, other.getHopCount());
        }
    }

    private static String toKey(Artifact artifact) {
        return artifact.getGroupId() + ":" + artifact.getArtifactId();
    }

    private static String toKey(Dependency dependency) {
        return dependency.getGroupId() + ":" + dependency.getArtifactId();
    }
}
