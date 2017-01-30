package com.github.javaparser.generator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.generator.utils.SourceRoot;

/**
 * A general pattern that the generators in this module will follow.
 */
public abstract class Generator {
    protected final JavaParser javaParser;
    protected final SourceRoot sourceRoot;

    protected Generator(JavaParser javaParser, SourceRoot sourceRoot) {
        this.javaParser = javaParser;
        this.sourceRoot = sourceRoot;
    }

    public abstract void generate() throws Exception;
}
