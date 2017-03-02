package com.github.javaparser.generator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.utils.SourceRoot;

/**
 * A general pattern that the generators in this module will follow.
 */
public abstract class Generator {
    protected final SourceRoot sourceRoot;

    protected Generator(SourceRoot sourceRoot) {
        this.sourceRoot = sourceRoot;
    }

    public abstract void generate() throws Exception;
}
