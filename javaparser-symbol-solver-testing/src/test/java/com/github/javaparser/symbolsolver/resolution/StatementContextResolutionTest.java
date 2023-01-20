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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
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
