package com.github.javaparser.generator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.JavaParserMetaModel;

public abstract class Generator {
    protected final JavaParser javaParser;
    protected final SourceRoot sourceRoot;
    protected final JavaParserMetaModel javaParserMetaModel;

    protected Generator(JavaParser javaParser, SourceRoot sourceRoot, JavaParserMetaModel javaParserMetaModel) {
        this.javaParser = javaParser;
        this.sourceRoot = sourceRoot;
        this.javaParserMetaModel = javaParserMetaModel;
    }

    public abstract void generate() throws Exception;
}
