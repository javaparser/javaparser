/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package org.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import org.javaparser.JavaParser;
import org.javaparser.ParseStart;
import org.javaparser.StreamProvider;
import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.expr.NameExpr;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;

class Issue2367Test extends AbstractSymbolResolutionTest {

    @Test
    void issue2367() throws IOException {
        Path dir = adaptPath("src/test/resources/issue2367");
        Path file = adaptPath("src/test/resources/issue2367/Issue2367.java");

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JavaParserTypeSolver(dir));

        JavaParser javaParser = new JavaParser();
        javaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();

        NameExpr nameExpr = unit.findFirst(NameExpr.class, m -> m.getName().getIdentifier().equals("privateField")).get();
        ResolvedValueDeclaration resolvedValueDeclaration = nameExpr.resolve();
        assertEquals("double", resolvedValueDeclaration.getType().describe());
    }
}
