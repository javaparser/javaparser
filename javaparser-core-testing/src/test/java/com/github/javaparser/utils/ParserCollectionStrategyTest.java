/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser.utils;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


class ParserCollectionStrategyTest {

    private static final ParserConfiguration parserConfig_java8 = new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8);
    private static final ParserConfiguration parserConfig_java9 = new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_9);

    @Test
    void getSourceRoots() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(ParserCollectionStrategyTest.class).resolve("").getParent();
        final ProjectRoot projectRoot = new ParserCollectionStrategy().collect(root);

        assertThat(projectRoot.getSourceRoots()).isNotEmpty();
        assertThat(projectRoot.getSourceRoot(root.resolve("javaparser-core/src/main/java"))).isNotEmpty();
        assertThat(projectRoot.getSourceRoot(root.resolve("javaparser-core-generators/src/main/java"))).isNotEmpty();
        assertThat(projectRoot.getSourceRoot(root.resolve("javaparser-core-metamodel-generator/src/main/java"))).isNotEmpty();
        assertThat(projectRoot.getSourceRoot(root.resolve("javaparser-symbol-solver-core/src/main/java"))).isNotEmpty();
    }


    @Test
    void rootAreFound_singleJavaFileInPackage() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/projectroot/issue2615/without_module_info");
        final ProjectRoot projectRoot = new ParserCollectionStrategy().collect(root);

        List<SourceRoot> sourceRoots = projectRoot.getSourceRoots();
        sourceRoots.forEach(System.out::println);

        assertEquals(1, sourceRoots.size());
        assertTrue(sourceRoots.get(0).getRoot().normalize().endsWith("without_module_info"));
    }

    @Test
    void rootsAreFound_withModuleInfoAndJavaFileInPackage() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/projectroot/issue2615/with_module_info");
        final ProjectRoot projectRoot = new ParserCollectionStrategy().collect(root);

        List<SourceRoot> sourceRoots = projectRoot.getSourceRoots();
        sourceRoots.forEach(System.out::println);

        assertEquals(1, sourceRoots.size());
        assertTrue(sourceRoots.get(0).getRoot().normalize().endsWith("with_module_info"));
    }

    @Test
    void rootsAreFound_withModuleInfoInRootAndJavaFileInPackage() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/projectroot/issue2615/with_module_info_in_root");
        final ProjectRoot projectRoot = new ParserCollectionStrategy(parserConfig_java9).collect(root);

        List<SourceRoot> sourceRoots = projectRoot.getSourceRoots();
        sourceRoots.forEach(System.out::println);

        assertEquals(1, sourceRoots.size());
        assertTrue(sourceRoots.get(0).getRoot().normalize().endsWith("with_module_info_in_root"));
    }

    @Test
    void rootsAreFound_parentOfMultipleSourceRootsWithAndWithoutModuleInfo() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/projectroot/issue2615");
        final ProjectRoot projectRoot = new ParserCollectionStrategy(parserConfig_java9).collect(root);

        List<SourceRoot> sourceRoots = projectRoot.getSourceRoots();

        for (SourceRoot sourceRoot : sourceRoots) {
            sourceRoot.getRoot().normalize().endsWith("with_module_info");
            System.out.println(sourceRoot);
        }

        assertEquals(3, sourceRoots.size());
    }


    @Test
    void manualInspectionOfSystemOut_callbackOnSourceRootParse_parentOfMultipleSourceRootsWithAndWithoutModuleInfo() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/projectroot/issue2615");
        final ProjectRoot projectRoot = new ParserCollectionStrategy(parserConfig_java9).collect(root);

        Callback cb = new Callback();

        final List<SourceRoot> sourceRoots = projectRoot.getSourceRoots();
        assertEquals(3, sourceRoots.size());

        sourceRoots.forEach(sourceRoot -> {
            try {
                sourceRoot.parse("", cb);
            } catch (IOException e) {
                System.err.println("IOException: " + e);
            }
        });


    }

    @Test
    void manualInspectionOfSystemOut_callbackOnSourceRootParse_singleJavaFileInPackage() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/projectroot/issue2615/without_module_info");
        final ProjectRoot projectRoot = new ParserCollectionStrategy().collect(root);

        Callback cb = new Callback();

        final List<SourceRoot> sourceRoots = projectRoot.getSourceRoots();
        assertEquals(1, sourceRoots.size());

        sourceRoots.forEach(sourceRoot -> {
            try {
                sourceRoot.parse("", cb);
            } catch (IOException e) {
                System.err.println("IOException: " + e);
            }
        });


    }

    @Test
    void manualInspectionOfSystemOut_callbackOnSourceRootParse_withModuleInfoAndJavaFileInPackage() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/projectroot/issue2615/with_module_info");
        final ProjectRoot projectRoot = new ParserCollectionStrategy().collect(root);

        Callback cb = new Callback();

        final List<SourceRoot> sourceRoots = projectRoot.getSourceRoots();
        assertEquals(1, sourceRoots.size());

        sourceRoots.forEach(sourceRoot -> {
            try {
                sourceRoot.parse("", cb);
            } catch (IOException e) {
                System.err.println("IOException: " + e);
            }
        });


    }

    @Test
    void manualInspectionOfSystemOut_callbackOnSourceRootParse_withModuleInfoInRootAndJavaFileInPackage() {
        final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/projectroot/issue2615/with_module_info_in_root");
        final ProjectRoot projectRoot = new ParserCollectionStrategy(parserConfig_java9).collect(root);

        Callback cb = new Callback();

        final List<SourceRoot> sourceRoots = projectRoot.getSourceRoots();
        assertEquals(1, sourceRoots.size());

        sourceRoots.forEach(sourceRoot -> {
            try {
                sourceRoot.parse("", cb);
            } catch (IOException e) {
                System.err.println("IOException: " + e);
            }
        });


    }


    private static class Callback implements SourceRoot.Callback {

        @Override
        public Result process(Path localPath, Path absolutePath, ParseResult<CompilationUnit> result) {
            System.out.printf("Found %s%n", absolutePath);
            return Result.SAVE;
        }
    }

}
