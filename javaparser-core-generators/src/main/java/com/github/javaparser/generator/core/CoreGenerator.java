package com.github.javaparser.generator.core;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.generator.core.node.*;
import com.github.javaparser.generator.core.other.TokenKindGenerator;
import com.github.javaparser.generator.core.visitor.*;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * Generates all generated visitors in the javaparser-core module.
 * Suggested usage is by running the run_core_generators.sh script.
 * You may want to run_metamodel_generator.sh before that.
 */
public class CoreGenerator {
    private static final ParserConfiguration parserConfiguration = new ParserConfiguration()
//                                .setStoreTokens(false)
//                                .setAttributeComments(false)
//                                .setLexicalPreservationEnabled(true)
            ;

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            throw new RuntimeException("Need 1 parameter: the JavaParser source checkout root directory.");
        }
        Log.setAdapter(new Log.StandardOutStandardErrorAdapter());
        final Path root = Paths.get(args[0], "..", "javaparser-core", "src", "main", "java");
        final SourceRoot sourceRoot = new SourceRoot(root, parserConfiguration)
//                .setPrinter(LexicalPreservingPrinter::print)
                ;

        final Path generatedJavaCcRoot = Paths.get(args[0], "..", "javaparser-core", "target", "generated-sources", "javacc");
        final SourceRoot generatedJavaCcSourceRoot = new SourceRoot(generatedJavaCcRoot, parserConfiguration)
//                .setPrinter(LexicalPreservingPrinter::print)
                ;

        new CoreGenerator().run(sourceRoot, generatedJavaCcSourceRoot);

        sourceRoot.saveAll();
    }

    private void run(SourceRoot sourceRoot, SourceRoot generatedJavaCcSourceRoot) throws Exception {
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
        new TokenKindGenerator(sourceRoot, generatedJavaCcSourceRoot).generate();
    }
}
