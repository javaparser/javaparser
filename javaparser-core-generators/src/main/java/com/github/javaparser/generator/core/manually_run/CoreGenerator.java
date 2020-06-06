/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.generator.core.manually_run;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.generator.core.node.*;
import com.github.javaparser.generator.core.other.BndGenerator;
import com.github.javaparser.generator.core.other.StaleGeneratorAnnotations;
import com.github.javaparser.generator.core.other.TokenKindGenerator;
import com.github.javaparser.generator.core.visitor.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;
import java.nio.file.Paths;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.RAW;

/**
 * Generates all generated visitors in the javaparser-core module.
 * Suggested usage is by running the run_core_generators.sh script.
 * You may want to run_metamodel_generator.sh before that.
 */
public class CoreGenerator {

    private static final ParserConfiguration parserConfiguration = new ParserConfiguration()
            .setLanguageLevel(RAW)
//            .setStoreTokens(false)
//            .setAttributeComments(false)
            .setLexicalPreservationEnabled(true)
            ;

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            throw new RuntimeException("Need 1 parameter: the JavaParser source checkout root directory.");
        }

        // Ensure that any log entries are output to the console.
        Log.setAdapter(new Log.StandardOutStandardErrorAdapter());

        // Specify the root dir of the JavaParser Core module
        final Path root_JavaParserCore = Paths.get(args[0], "..", "javaparser-core", "src", "main", "java");

        // Why is this required?
        // `SourceRoot#tryToParse` creates a new instance of `JavaParser`,
        // AND the config is passed via the constructor to SourceRoot
        StaticJavaParser.setConfiguration(parserConfiguration);

        //
        final SourceRoot sourceRoot = new SourceRoot(root_JavaParserCore, parserConfiguration)
                .setPrinter(LexicalPreservingPrinter::print) // TODO: Why is this required if it is already set within the config? See also #2703
                ;

        //
        final Path generatedJavaCcRoot = Paths.get(args[0], "..", "javaparser-core", "target", "generated-sources", "javacc");
        final SourceRoot generatedJavaCcSourceRoot = new SourceRoot(generatedJavaCcRoot, parserConfiguration)
                .setPrinter(LexicalPreservingPrinter::print) // TODO: Why is this required if it is already set within the config? See also #2703
                ;


        // First remove all @Generated() annotations.
        // Note that the generators below should replace them, meaning no substantial git diffs.
        // Exceptions to this occur when e.g. a field/property is renamed/removed.
        StaleGeneratorAnnotations staleGeneratorAnnotations = new StaleGeneratorAnnotations(sourceRoot);
        staleGeneratorAnnotations.generate();

        // Do the generating
        new CoreGenerator().run(sourceRoot, generatedJavaCcSourceRoot);

        // Remove unused stale imports
        staleGeneratorAnnotations.removeStaleImportIfUnused();
        staleGeneratorAnnotations.removeGeneratedImportIfUnused();

        // Write the generated code to storage.
        sourceRoot.saveAll();

        // Verify that there are no leftover @StaleGenerated annotations remaining.
        staleGeneratorAnnotations.verify();

        // TODO: Include some form of statistics within the output.
    }

    private void run(SourceRoot sourceRoot, SourceRoot generatedJavaCcSourceRoot) throws Exception {

        // Run generators -- extends AbstractNodeGenerator ((mostly visitor stuff?))
        new CloneVisitorGenerator(sourceRoot).generate();
        new EqualsVisitorGenerator(sourceRoot).generate();
        new GenericListVisitorAdapterGenerator(sourceRoot).generate();
        new GenericVisitorAdapterGenerator(sourceRoot).generate();
        new GenericVisitorGenerator(sourceRoot).generate();
        new GenericVisitorWithDefaultsGenerator(sourceRoot).generate();
        new HashCodeVisitorGenerator(sourceRoot).generate();
        new ModifierVisitorGenerator(sourceRoot).generate();
        new NoCommentEqualsVisitorGenerator(sourceRoot).generate();
        new NoCommentHashCodeVisitorGenerator(sourceRoot).generate();
        new ObjectIdentityEqualsVisitorGenerator(sourceRoot).generate();
        new ObjectIdentityHashCodeVisitorGenerator(sourceRoot).generate();
        new VoidVisitorAdapterGenerator(sourceRoot).generate();
        new VoidVisitorGenerator(sourceRoot).generate();
        new VoidVisitorWithDefaultsGenerator(sourceRoot).generate();

        //
        new TypeCastingGenerator(sourceRoot).generate(); // Not visitor-related, but extends AbstractNodeGenerator?

        // Run generators -- extends AbstractGenerator
        new AcceptGenerator(sourceRoot).generate();
        new CloneGenerator(sourceRoot).generate();
        new GetMetaModelGenerator(sourceRoot).generate();
        new MainConstructorGenerator(sourceRoot).generate();
        new NodeModifierGenerator(sourceRoot).generate();
        new PropertyGenerator(sourceRoot).generate();
        new RemoveMethodGenerator(sourceRoot).generate();
        new ReplaceMethodGenerator(sourceRoot).generate();

        // Run generators -- grammar/tokens
        new TokenKindGenerator(sourceRoot, generatedJavaCcSourceRoot).generate(); // TODO/FIXME: Lexical preserving indentation for enums.

        // Finally, do BndGenerator once everything is sorted.
        new BndGenerator(sourceRoot).generate();
    }
}
