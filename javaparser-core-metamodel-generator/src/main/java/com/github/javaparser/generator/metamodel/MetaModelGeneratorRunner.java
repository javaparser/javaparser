package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.printer.PrettyPrinterConfiguration;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;
import java.nio.file.Paths;

public class MetaModelGeneratorRunner {

    public static void main(String[] args) throws NoSuchMethodException {
        // Process input args.
        if (args.length != 1) {
            throw new RuntimeException("Need 1 parameter: the JavaParser source checkout root directory.");
        }
        final Path root = Paths.get(args[0], "..", "javaparser-core", "src", "main", "java");

        // Setup JP
        final ParserConfiguration parserConfiguration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.RAW)
                .setStoreTokens(false);

        final SourceRoot sourceRoot = new SourceRoot(root, parserConfiguration);
        sourceRoot.setPrinter(new PrettyPrinter(new PrettyPrinterConfiguration().setEndOfLineCharacter("\n"))::print);
        StaticJavaParser.setConfiguration(parserConfiguration);

        // Run Generators.
        new MetaModelGenerator().run(sourceRoot);

        // Commit changes to disk.
        sourceRoot.saveAll();
    }

}
