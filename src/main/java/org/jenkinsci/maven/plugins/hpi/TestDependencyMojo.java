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
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.NavigableSet;
import java.util.Properties;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
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
     * Must correspond to dependencies already present in the project model or their transitive dependencies.
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

        Set<MavenArtifact> effectiveArtifacts;
        Map<String, String> additions = new HashMap<>();
        Map<String, String> deletions = new HashMap<>();
        Map<String, String> updates = new HashMap<>();
        if (overrides.isEmpty()) {
            effectiveArtifacts = getProjectArtfacts();
        } else {
            // TODO under no circumstances should this code ever be executed when performing a release

            // Create a shadow project for dependency analysis.
            MavenProject shadow = project.clone();

            // Stash the original resolution for use later.
            Map<String, String> originalResolution = new HashMap<>();
            for (Artifact artifact : shadow.getArtifacts()) {
                originalResolution.put(toKey(artifact), artifact.getVersion());
            }

            // First pass: apply the overrides specified by the user.
            pass(overrides, shadow, getLog());

            if (useUpperBounds) {
                /*
                 * Do upper bounds analysis. Upper bounds analysis consumes the model directly and
                 * not the resolution of that model, so it is fine to invoke it at this point with
                 * the model having been updated and the resolution having been cleared.
                 */
                DependencyNode node;
                try {
                    ProjectBuildingRequest buildingRequest =
                            new DefaultProjectBuildingRequest(session.getProjectBuildingRequest());
                    buildingRequest.setProject(shadow);
                    ArtifactFilter filter = null; // Evaluate all scopes
                    node = dependencyCollectorBuilder.collectDependencyGraph(buildingRequest, filter);
                } catch (DependencyCollectorBuilderException x) {
                    throw new MojoExecutionException("could not analyze dependency tree for useUpperBounds: " + x, x);
                }
                RequireUpperBoundDepsVisitor visitor = new RequireUpperBoundDepsVisitor();
                node.accept(visitor);
                Map<String, String> upperBounds = visitor.upperBounds();

                // TODO is this check overkill?
                for (String dep : upperBounds.keySet()) {
                    if (overrides.containsKey(dep)) {
                        throw new AssertionError("overrides should not contain dependency " + dep + " that was inferred by upper bounds");
                    }
                }

                // Second pass: apply the results of the upper bounds analysis.
                pass(upperBounds, shadow, getLog());
            }

            /*
             * At this point, the model has been updated as the user has requested. We now redo
             * resolution and compare the new resolution to the original in order to account for
             * updates to transitive dependencies that are not present in the model. Anything that
             * was removed in the new resolution needs to be removed from the test classpath.
             * Anything that was added in the new resolution needs to be added to the test
             * classpath.
             */
            Set<Artifact> resolved = resolveDependencies(shadow);
            effectiveArtifacts = wrap(new Artifacts(resolved));
            Map<String, String> newResolution = new HashMap<>();
            for (Artifact artifact : resolved) {
                newResolution.put(toKey(artifact), artifact.getVersion());
            }
            for (Map.Entry<String, String> entry : newResolution.entrySet()) {
                if (originalResolution.containsKey(entry.getKey())) {
                    // Present in both old and new resolution: check for update.
                    String originalVersion = originalResolution.get(entry.getKey());
                    String newVersion = entry.getValue();
                    if (!newVersion.equals(originalVersion)) {
                        updates.put(entry.getKey(), newVersion);
                    }
                } else {
                    // Present in new resolution but not old: addition.
                    additions.put(entry.getKey(), entry.getValue());
                }
            }
            for (Map.Entry<String, String> entry : originalResolution.entrySet()) {
                if (!newResolution.containsKey(entry.getKey())) {
                    // Present in old resolution but not new: deletion.
                    deletions.put(entry.getKey(), entry.getValue());
                }
            }
            getLog().debug("after re-resolving, additions: " + additions);
            getLog().debug("after re-resolving, deletions: " + deletions);
            getLog().debug("after re-resolving, updates: " + updates);
        }

        File testDir = new File(project.getBuild().getTestOutputDirectory(), "test-dependencies");
        try {
            Files.createDirectories(testDir.toPath());
        } catch (IOException e) {
            throw new MojoExecutionException("Failed to create directories for '" + testDir + "'", e);
        }

        try (FileOutputStream fos = new FileOutputStream(new File(testDir, "index")); Writer w = new OutputStreamWriter(fos, StandardCharsets.UTF_8)) {
            for (MavenArtifact a : effectiveArtifacts) {
                if (!a.isPluginBestEffort(getLog()))
                    continue;

                String artifactId = a.getActualArtifactId();
                if (artifactId == null) {
                    getLog().debug("Skipping " + artifactId + " with classifier " + a.getClassifier());
                    continue;
                }

                getLog().debug("Copying " + artifactId + " as a test dependency");
                File dst = new File(testDir, artifactId + ".hpi");
                FileUtils.copyFile(a.getHpi().getFile(),dst);
                w.write(artifactId + "\n");
            }
        } catch (IOException e) {
            throw new MojoExecutionException("Failed to copy dependency plugins",e);
        }

        if (!additions.isEmpty() || !deletions.isEmpty() || !updates.isEmpty()) {
            List<String> additionalClasspathElements = new LinkedList<>();
            NavigableMap<String, String> includes = new TreeMap<>();
            includes.putAll(additions);
            includes.putAll(updates);
            for (Map.Entry<String, String> entry : includes.entrySet()) {
                String key = entry.getKey();
                String[] groupArt = key.split(":");
                String groupId = groupArt[0];
                String artifactId = groupArt[1];
                String version = entry.getValue();
                // Cannot use MavenProject.getArtifactMap since we may have multiple dependencies of different classifiers.
                boolean found = false;
                for (MavenArtifact a : effectiveArtifacts) {
                    if (!a.getGroupId().equals(groupId) || !a.getArtifactId().equals(artifactId)) {
                        continue;
                    }
                    if (!a.getVersion().equals(version)) {
                        throw new AssertionError("should never happen");
                    }
                    found = true;
                    if (a.getArtifactHandler().isAddedToClasspath()) { // everything is added to test CP, so no need to check scope
                        additionalClasspathElements.add(a.getFile().getAbsolutePath());
                    }
                }
                if (!found) {
                    throw new MojoExecutionException("could not find dependency " + key);
                }
            }

            NavigableSet<String> classpathDependencyExcludes = new TreeSet<>();
            classpathDependencyExcludes.addAll(deletions.keySet());
            classpathDependencyExcludes.addAll(updates.keySet());

            Properties properties = project.getProperties();
            getLog().info("Replacing POM-defined classpath elements " + classpathDependencyExcludes + " with " + additionalClasspathElements);
            // cf. http://maven.apache.org/surefire/maven-surefire-plugin/test-mojo.html
            properties.setProperty("maven.test.additionalClasspath", String.join(",", additionalClasspathElements));
            properties.setProperty("maven.test.dependency.excludes", String.join(",", classpathDependencyExcludes));
        }
    }

    /**
     * Apply the overrides specified by the user or upper bounds analysis to the model (i.e.,
     * dependency management or dependencies) in the shadow project. This clears the existing
     * resolution that was done because of the {@code @requiresDependencyResolution} Mojo attribute,
     * as it is now invalid. It is possible to perform such a pass manually on a plugin and compare
     * the results with this algorithm to verify that the logic in this method is correct.
     */
    private static void pass(Map<String, String> overrides, MavenProject project, Log log) throws MojoFailureException {
        Set<String> updates = new HashSet<>();

        // Update existing dependency entries in the model.
        for (Dependency dependency : project.getDependencies()) {
            if (updateDependency(overrides, dependency, log)) {
                updates.add(toKey(dependency));
            }
        }

        // Update existing dependency management entries in the model.
        if (project.getDependencyManagement() != null) {
            for (Dependency dependency : project.getDependencyManagement().getDependencies()) {
                if (updateDependency(overrides, dependency, log)) {
                    updates.add(toKey(dependency));
                }
            }
        }

        // Track that we have applied some of the user's request by now.
        Set<String> unappliedDependencies = new HashSet<>(overrides.keySet());
        unappliedDependencies.removeAll(updates);

        /*
         * If an override was requested for a transitive dependency that is not in the model, add a dependency
         * management entry to the model.
         */
        Set<String> additions = new HashSet<>();
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
                if (project.getDependencyManagement() != null) {
                    project.getDependencyManagement().addDependency(dependency);
                } else {
                    throw new IllegalStateException("Failed to override " + key + " to " + overrides.get(key) + " because the project does not have a dependency management section");
                }
                additions.add(key);
            }
        }
        unappliedDependencies.removeAll(additions);

        // By now, we should have applied the entire request. If not, fail.
        if (!unappliedDependencies.isEmpty()) {
            throw new MojoFailureException("could not find dependencies " + unappliedDependencies);
        }
        log.debug("adjusted dependencies: " + project.getDependencies());
        if (project.getDependencyManagement() != null) {
            log.debug("adjusted dependency management: " + project.getDependencyManagement().getDependencies());
        }

        /*
         * With our changes to the model, the existing resolution is now invalid, so clear it lest
         * anything accidentally use the invalid values. We will perform resolution again after all
         * passes are complete.
         */
        project.setDependencyArtifacts(null);
        project.setArtifacts(null);
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
                        String key = toKey(artifact);
                        if (!r.containsKey(key) || new ComparableVersion(version.toString()).compareTo(new ComparableVersion(r.get(key))) > 1) {
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
