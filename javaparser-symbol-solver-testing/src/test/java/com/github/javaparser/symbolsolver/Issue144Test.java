/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue144Test extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        Path srcDir = adaptPath("src/test/resources/issue144");
        typeSolver = new JavaParserTypeSolver(srcDir, new LeanParserConfiguration());
    }

    @Test
    void issue144() {
        CompilationUnit cu = parseSampleWithStandardExtension("issue144/HelloWorld");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "HelloWorld");
        ExpressionStmt expressionStmt = (ExpressionStmt)clazz.getMethodsByName("main").get(0).getBody().get().getStatement(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) expressionStmt.getExpression();
        Expression firstParameter = methodCallExpr.getArgument(0);
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        assertEquals(true, javaParserFacade.solve(firstParameter).isSolved());
        assertEquals(true, javaParserFacade.solve(firstParameter).getCorrespondingDeclaration().isField());
        assertEquals("hw", javaParserFacade.solve(firstParameter).getCorrespondingDeclaration().getName());
    }

    @Test
    void issue144WithReflectionTypeSolver() {
        CompilationUnit cu = parseSampleWithStandardExtension("issue144/HelloWorld");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "HelloWorld");
        ExpressionStmt expressionStmt = (ExpressionStmt)clazz.getMethodsByName("main").get(0).getBody().get().getStatement(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) expressionStmt.getExpression();
        Expression firstParameter = methodCallExpr.getArgument(0);
        JavaParserFacade javaParserFacade = JavaParserFacade.get(new ReflectionTypeSolver(true));

        assertEquals(true, javaParserFacade.solve(firstParameter).isSolved());
    }

    @Test
    void issue144WithCombinedTypeSolver() {
        CompilationUnit cu = parseSampleWithStandardExtension("issue144/HelloWorld");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "HelloWorld");
        ExpressionStmt expressionStmt = (ExpressionStmt)clazz.getMethodsByName("main").get(0).getBody().get().getStatement(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) expressionStmt.getExpression();
        Expression firstParameter = methodCallExpr.getArgument(0);
        JavaParserFacade javaParserFacade = JavaParserFacade.get(new CombinedTypeSolver(typeSolver, new ReflectionTypeSolver(true)));

        assertEquals(true, javaParserFacade.solve(firstParameter).isSolved());
    }
}
