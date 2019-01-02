/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.LambdaExprContext;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
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

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        MethodDeclaration method = Navigator.demandMethod(clazz, "lambdaMap");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);
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

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
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

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
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
