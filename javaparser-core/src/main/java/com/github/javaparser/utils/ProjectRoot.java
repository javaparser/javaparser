package com.github.javaparser.utils;

import com.github.javaparser.ParserConfiguration;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The structure of a Java project directory.
 * It was originally created specifically to quickly configure the symbol solver.
 * You can use it as a general container for project information.
 * <p/>A project has a root directory, and it has zero or more directories that contain source code.
 * <p/>To create a ProjectRoot use a CollectionStrategy, or instantiate ProjectRoot yourself.
 */
public class ProjectRoot {

    private final Path root;
    private final Map<Path, SourceRoot> sourceRoots = new ConcurrentHashMap<>();
    private final List<Path> jarFiles = new ArrayList<>();
    private final ParserConfiguration parserConfiguration;

    public ProjectRoot(Path projectRoot) {
        this(projectRoot, new ParserConfiguration());
    }

    public ProjectRoot(Path projectRoot, ParserConfiguration parserConfiguration) {
        this.root = projectRoot;
        this.parserConfiguration = parserConfiguration;
    }

    public Optional<SourceRoot> getSourceRoot(Path sourceRoot) {
        return Optional.ofNullable(sourceRoots.get(sourceRoot));
    }

    public List<SourceRoot> getSourceRoots() {
        return new ArrayList<>(sourceRoots.values());
    }

    public void addSourceRoot(Path path) {
        addSourceRoot(new SourceRoot(path, parserConfiguration));
    }

    public void addSourceRoot(SourceRoot sourceRoot) {
        sourceRoot.setParserConfiguration(parserConfiguration);
        sourceRoots.put(sourceRoot.getRoot(), sourceRoot);
    }

    /**
     * @deprecated use getRoot()
     */
    @Deprecated
    public Path getProjectRoot() {
        return root;
    }

    public Path getRoot() {
        return root;
    }

    public void addJarFile(Path jarFile) {
        jarFiles.add(jarFile);
    }

    public List<Path> getJarFiles() {
        return jarFiles;
    }
}
