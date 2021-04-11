/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

package com.github.javaparser.generator.core;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.generator.core.node.AcceptGenerator;
import com.github.javaparser.generator.core.node.CloneGenerator;
import com.github.javaparser.generator.core.node.GetMetaModelGenerator;
import com.github.javaparser.generator.core.node.MainConstructorGenerator;
import com.github.javaparser.generator.core.node.NodeModifierGenerator;
import com.github.javaparser.generator.core.node.PropertyGenerator;
import com.github.javaparser.generator.core.node.RemoveMethodGenerator;
import com.github.javaparser.generator.core.node.ReplaceMethodGenerator;
import com.github.javaparser.generator.core.node.TypeCastingGenerator;
import com.github.javaparser.generator.core.other.BndGenerator;
import com.github.javaparser.generator.core.other.TokenKindGenerator;
import com.github.javaparser.generator.core.visitor.CloneVisitorGenerator;
import com.github.javaparser.generator.core.visitor.EqualsVisitorGenerator;
import com.github.javaparser.generator.core.visitor.GenericListVisitorAdapterGenerator;
import com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator;
import com.github.javaparser.generator.core.visitor.GenericVisitorGenerator;
import com.github.javaparser.generator.core.visitor.GenericVisitorWithDefaultsGenerator;
import com.github.javaparser.generator.core.visitor.HashCodeVisitorGenerator;
import com.github.javaparser.generator.core.visitor.ModifierVisitorGenerator;
import com.github.javaparser.generator.core.visitor.NoCommentEqualsVisitorGenerator;
import com.github.javaparser.generator.core.visitor.NoCommentHashCodeVisitorGenerator;
import com.github.javaparser.generator.core.visitor.ObjectIdentityEqualsVisitorGenerator;
import com.github.javaparser.generator.core.visitor.ObjectIdentityHashCodeVisitorGenerator;
import com.github.javaparser.generator.core.visitor.VoidVisitorAdapterGenerator;
import com.github.javaparser.generator.core.visitor.VoidVisitorGenerator;
import com.github.javaparser.generator.core.visitor.VoidVisitorWithDefaultsGenerator;
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
    private static final ParserConfiguration PARSER_CONFIGURATION = new ParserConfiguration()
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
        final Path root = Paths.get(args[0], "..", "javaparser-core", "src", "main", "java");
        final SourceRoot sourceRoot = new SourceRoot(root, PARSER_CONFIGURATION)
//                .setPrinter(LexicalPreservingPrinter::print)
                ;
        StaticJavaParser.setConfiguration(PARSER_CONFIGURATION);

        final Path generatedJavaCcRoot = Paths.get(args[0], "..", "javaparser-core", "target", "generated-sources", "javacc");
        final SourceRoot generatedJavaCcSourceRoot = new SourceRoot(generatedJavaCcRoot, PARSER_CONFIGURATION)
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
        new NodeModifierGenerator(sourceRoot).generate();
        new AcceptGenerator(sourceRoot).generate();
        new TokenKindGenerator(sourceRoot, generatedJavaCcSourceRoot).generate();
        new BndGenerator(sourceRoot).generate();
    }
}
