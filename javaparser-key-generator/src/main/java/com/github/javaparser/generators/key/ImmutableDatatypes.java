package com.github.javaparser.generators.key;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.RAW;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class ImmutableDatatypes {
    private static final ParserConfiguration parserConfiguration = new ParserConfiguration()
            .setLanguageLevel(RAW)
//                                .setStoreTokens(false)
//                                .setAttributeComments(false)
//                                .setLexicalPreservationEnabled(true)
            ;

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            throw new RuntimeException("Need 1 parameter: the JavaParser source checkout root directory.");
        }
        Log.setAdapter(new Log.StandardOutStandardErrorAdapter());
        final Path sourceDirectory = Paths.get(args[0], "..", "javaparser-core", "src", "main", "java");
        final SourceRoot sourceRoot = new SourceRoot(sourceDirectory, parserConfiguration)
//                .setPrinter(LexicalPreservingPrinter::print)
                ;

        final Path outputDirectory = Paths.get(args[0], "..", "target", "src-key");

        StaticJavaParser.setConfiguration(parserConfiguration);

        final Path generatedJavaCcRoot = Paths.get(args[0], "..", "javaparser-core", "target", "generated-sources", "javacc");
        final SourceRoot generatedJavaCcSourceRoot = new SourceRoot(generatedJavaCcRoot, parserConfiguration)
//                .setPrinter(LexicalPreservingPrinter::print)
                ;
        new ImmutableDatatypes().run(sourceRoot, generatedJavaCcSourceRoot, outputDirectory);
        sourceRoot.saveAll();
    }

    private void run(SourceRoot sourceRoot, SourceRoot generatedJavaCcSourceRoot, Path outputDirectory) throws Exception {
        Files.createDirectories(outputDirectory);
        //new CopyNodeGenerator(sourceRoot, outputDirectory).generate();
        //new CopyVisitorGenerator(sourceRoot, outputDirectory).generate();
        new FreezeVisitorGenerator(sourceRoot, outputDirectory).generate();
    }
}
