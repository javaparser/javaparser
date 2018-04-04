package com.github.javaparser.utils;

import java.nio.file.Path;

public class CollectionContext {

    private CollectionStrategy strategy;

    public CollectionContext(CollectionStrategy strategy) {
        this.strategy = strategy;
    }

    public ProjectRoot collect(Path path) {
        return strategy.collect(path);
    }
}
