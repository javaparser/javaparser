package com.github.javaparser.utils;

import java.nio.file.Path;

/**
 * Set the strategy to be applied for collecting files for the ProjectRoot.
 */
public class CollectionContext {

    private CollectionStrategy strategy;

    public CollectionContext(CollectionStrategy strategy) {
        this.strategy = strategy;
    }

    public ProjectRoot collect(Path path) {
        return strategy.collect(path);
    }
}
