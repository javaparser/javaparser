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

package org.javaparser.symbolsolver.resolution.javaparser.contexts;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.body.VariableDeclarator;
import org.javaparser.ast.expr.LambdaExpr;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.ast.stmt.ReturnStmt;
import org.javaparser.symbolsolver.core.resolution.Context;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.contexts.LambdaExprContext;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.model.resolution.Value;
import org.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Malte Langkabel
 */
class LambdaExprContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
    }

    @Test
    void solveParameterOfLambdaInMethodCallExpr() {
        CompilationUnit cu = parseSample("Lambda");

        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        MethodDeclaration method = Navigator.demandMethod(clazz, "lambdaMap");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodCallExpr methodCallExpr = (MethodCallExpr) returnStmt.getExpression().get();
        LambdaExpr lambdaExpr = (LambdaExpr) methodCallExpr.getArguments().get(0);

        Context context = new LambdaExprContext(lambdaExpr, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("p");
        assertTrue(ref.isPresent());
        assertEquals("? super java.lang.String", ref.get().getType().describe());
    }

    @Test
    void solveParameterOfLambdaInFieldDecl() {
        CompilationUnit cu = parseSample("Lambda");

        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        VariableDeclarator field = Navigator.demandField(clazz, "functional");
        LambdaExpr lambdaExpr = (LambdaExpr) field.getInitializer().get();

        Path src = Paths.get("src/test/resources");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath(src), new LeanParserConfiguration()));

        Context context = new LambdaExprContext(lambdaExpr, combinedTypeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("p");
        assertTrue(ref.isPresent());
        assertEquals("java.lang.String", ref.get().getType().describe());
    }

    @Test
    void solveParameterOfLambdaInVarDecl() {
        CompilationUnit cu = parseSample("Lambda");

        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testFunctionalVar");
        VariableDeclarator varDecl = Navigator.demandVariableDeclaration(method, "a").get();
        LambdaExpr lambdaExpr = (LambdaExpr) varDecl.getInitializer().get();

        Path src = adaptPath("src/test/resources");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));

        Context context = new LambdaExprContext(lambdaExpr, combinedTypeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("p");
        assertTrue(ref.isPresent());
        assertEquals("java.lang.String", ref.get().getType().describe());
    }
}
