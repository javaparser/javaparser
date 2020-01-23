/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package org.javaparser.symbolsolver.javassistmodel;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.stmt.ExpressionStmt;
import org.javaparser.ast.stmt.Statement;
import org.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.javaparser.StaticJavaParser.parse;

class Issue257Test extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/issue257/issue257.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());
    }

    @Test
    void verifyBCanBeSolved() {
        typeSolver.solveType("net.testbug.B");
    }

    @Test
    void issue257() throws IOException {
        Path pathToSourceFile = adaptPath("src/test/resources/issue257/A.java.txt");
        CompilationUnit cu = parse(pathToSourceFile);
        Statement statement = cu.getClassByName("A").get().getMethodsByName("run").get(0).getBody().get().getStatement(0);
        ExpressionStmt expressionStmt = (ExpressionStmt)statement;
        Expression expression = expressionStmt.getExpression();
        JavaParserFacade.get(typeSolver).getType(expression);
    }

}
