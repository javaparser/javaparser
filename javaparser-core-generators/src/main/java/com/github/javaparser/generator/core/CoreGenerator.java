package com.github.javaparser.generator.core;

import com.github.javaparser.JavaParser;
import com.github.javaparser.generator.core.node.GetNodeListsGenerator;
import com.github.javaparser.generator.core.node.PropertyGenerator;
import com.github.javaparser.generator.core.node.RemoveNodeMethodGenerator;
import com.github.javaparser.generator.core.visitor.*;
import com.github.javaparser.generator.utils.GeneratorUtils;
import com.github.javaparser.generator.utils.SourceRoot;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * Generates all generated visitors in the javaparser-core module.
 */
public class CoreGenerator {
    public static void main(String[] args) throws Exception {
        Path root = GeneratorUtils.getJavaParserBasePath().resolve(Paths.get("javaparser-core", "src", "main", "java"));

        final JavaParser javaParser = new JavaParser();

        final SourceRoot sourceRoot = new SourceRoot(root);

        new GenericVisitorAdapterGenerator(javaParser, sourceRoot).generate();
        new EqualsVisitorGenerator(javaParser, sourceRoot).generate();
        new VoidVisitorAdapterGenerator(javaParser, sourceRoot).generate();
        new VoidVisitorGenerator(javaParser, sourceRoot).generate();
        new GenericVisitorGenerator(javaParser, sourceRoot).generate();
        new HashCodeVisitorGenerator(javaParser, sourceRoot).generate();
        new CloneVisitorGenerator(javaParser, sourceRoot).generate();
        new TreeStructureVisitorGenerator(javaParser, sourceRoot).generate();

        new GetNodeListsGenerator(javaParser, sourceRoot).generate();
        new PropertyGenerator(javaParser, sourceRoot).generate();
        new RemoveNodeMethodGenerator(javaParser, sourceRoot).generate();

        sourceRoot.saveAll();
    }
}
