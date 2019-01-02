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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class StatementContextResolutionTest extends AbstractResolutionTest {

    @Test
    void resolveLocalVariableInParentOfParent() {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo1");
        NameExpr nameExpr = Navigator.findNameExpression(method, "s").get();

        SymbolReference<? extends ResolvedValueDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(nameExpr);
        assertTrue(ref.isSolved());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    void resolveLocalVariableInParent() {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo3");
        NameExpr nameExpr = Navigator.findNameExpression(method, "s").get();

        SymbolReference<? extends ResolvedValueDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(nameExpr);
        assertTrue(ref.isSolved());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    void resolveLocalVariableInSameParent() {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo2");
        NameExpr nameExpr = Navigator.findNameExpression(method, "s").get();

        SymbolReference<? extends ResolvedValueDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(nameExpr);
        assertTrue(ref.isSolved());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    void resolveLocalAndSeveralAnnidatedLevels() {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo4");
        MethodCallExpr call = Navigator.findMethodCall(method, "add").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();

        SymbolReference<? extends ResolvedValueDeclaration> ref = JavaParserFacade.get(typeSolver).solve(call.getScope().get());
        assertTrue(ref.isSolved());
        assertEquals("java.util.List<Comment>", ref.getCorrespondingDeclaration().getType().describe());

        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);
        assertEquals("add", methodUsage.getName());
    }

    @Test
    void resolveMethodOnGenericClass() {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo5");
        MethodCallExpr call = Navigator.findMethodCall(method, "add").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();

        SymbolReference<? extends ResolvedValueDeclaration> ref = JavaParserFacade.get(typeSolver).solve(call.getScope().get());
        assertTrue(ref.isSolved());
        assertEquals("java.util.List<Comment>", ref.getCorrespondingDeclaration().getType().describe());

        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);
        assertEquals("add", methodUsage.getName());
    }

}
