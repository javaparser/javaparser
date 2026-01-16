/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class Issue4846Test extends AbstractResolutionTest {
    public static final Path SRC_DIR = adaptPath("src/test/resources/issue4846");

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new JavaParserTypeSolver(SRC_DIR))))
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16);

        javaParser = new JavaParser(configuration);
    }

    @Test
    void test() throws IOException {
        CompilationUnit cu = javaParser
                .parse(SRC_DIR.resolve("foo").resolve("Main.java"))
                .getResult()
                .get();
        TypeDeclaration<?> typeDec = cu.getType(0);
        MethodDeclaration methodDec = typeDec.getMethodsByName("foo").get(0);
        assertDoesNotThrow(methodDec::toDescriptor);
    }
}
