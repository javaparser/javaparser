package com.github.javaparser.generator.core;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.generator.core.node.*;
import com.github.javaparser.generator.core.visitor.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * Generates all generated visitors in the javaparser-core module.
 */
public class CoreGenerator {
    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            throw new RuntimeException("Need 1 parameter: the JavaParser source checkout root directory.");
        }
        final Path root = Paths.get(args[0], "..", "javaparser-core", "src", "main", "java");
        final SourceRoot sourceRoot = new SourceRoot(root)
//                .setPrinter(LexicalPreservingPrinter::print)
                .setJavaParser(new JavaParser(
                        new ParserConfiguration()
//                                .setStoreTokens(false)
//                                .setAttributeComments(false)
//                                .setLexicalPreservationEnabled(true)
                ));

        new CoreGenerator().run(sourceRoot);

        sourceRoot.saveAll();
    }

    private void run(SourceRoot sourceRoot) throws Exception {
        new TypeCastingGenerator(sourceRoot).generate();
        new GenericListVisitorAdapterGenerator(sourceRoot).generate();
        new GenericVisitorAdapterGenerator(sourceRoot).generate();
        new GenericVisitorWithDefaultsGenerator(sourceRoot).generate();
        new EqualsVisitorGenerator(sourceRoot).generate();
        new ObjectIdentityEqualsVisitorGenerator(sourceRoot).generate();
        new NoCommentEqualsVisitorGenerator(sourceRoot).generate();
        new VoidVisitorAdapterGenerator(sourceRoot).generate();
        new VoidVisitorGenerator(sourceRoot).generate();
        new VoidVisitorWithDefaultsGenerator(sourceRoot).generate();
        new GenericVisitorGenerator(sourceRoot).generate();
        new HashCodeVisitorGenerator(sourceRoot).generate();
        new ObjectIdentityHashCodeVisitorGenerator(sourceRoot).generate();
        new NoCommentHashCodeVisitorGenerator(sourceRoot).generate();
        new CloneVisitorGenerator(sourceRoot).generate();
        new ModifierVisitorGenerator(sourceRoot).generate();

        new PropertyGenerator(sourceRoot).generate();
        new RemoveMethodGenerator(sourceRoot).generate();
        new ReplaceMethodGenerator(sourceRoot).generate();
        new CloneGenerator(sourceRoot).generate();
        new GetMetaModelGenerator(sourceRoot).generate();
        new MainConstructorGenerator(sourceRoot).generate();
        new FinalGenerator(sourceRoot).generate();
        new AcceptGenerator(sourceRoot).generate();
    }
}
