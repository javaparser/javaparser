package com.github.javaparser.utils;

import com.github.javaparser.ParserConfiguration;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Find and to compile all files in a project folder, which results in a collection of SourceRoots.
 * To populate the ProjectRoot, set the CollectionStrategy in the CollectionContext to collect the required files.
 */
public class ProjectRoot {

    private final Path projectRoot;
    private final Map<Path, SourceRoot> cache = new ConcurrentHashMap<>();
    private ParserConfiguration parserConfiguration = new ParserConfiguration();

    public ProjectRoot(Path projectRoot) {
        this.projectRoot = projectRoot;
    }

    public ProjectRoot(Path projectRoot, ParserConfiguration parserConfiguration) {
        this.projectRoot = projectRoot;
        this.parserConfiguration = parserConfiguration;
    }

    public Optional<SourceRoot> getSourceRoot(Path sourceRoot) {
        return Optional.ofNullable(cache.get(sourceRoot));
    }

    public List<SourceRoot> getSourceRoots() {
        return new ArrayList<>(cache.values());
    }

    public void addSourceRoot(Path path) {
        cache.put(path, new SourceRoot(path).setParserConfiguration(parserConfiguration));
    }

    public Path getProjectRoot() {
        return projectRoot;
    }
}
