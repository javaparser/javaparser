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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserAnonymousClassDeclarationTest extends AbstractResolutionTest {

  @Test
  void anonymousClassAsMethodArgument() {
    CompilationUnit cu = parseSample("AnonymousClassDeclarations");
    ClassOrInterfaceDeclaration aClass = Navigator.demandClass(cu, "AnonymousClassDeclarations");
    MethodDeclaration method = Navigator.demandMethod(aClass, "fooBar1");
    MethodCallExpr methodCall = Navigator.findMethodCall(method, "of").get();

    CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
    combinedTypeSolver.add(new ReflectionTypeSolver());
    MethodUsage methodUsage =
        JavaParserFacade.get(combinedTypeSolver).solveMethodAsUsage(methodCall);

    assertThat(methodUsage.getDeclaration().getQualifiedSignature(),
            is("AnonymousClassDeclarations.ParDo.of(AnonymousClassDeclarations.DoFn<I, O>)"));
    assertThat(methodUsage.getQualifiedSignature(),
               is("AnonymousClassDeclarations.ParDo.of(AnonymousClassDeclarations.DoFn<java.lang.Integer, java.lang.Long>)"));
  }

  @Test
  void callingSuperClassInnerClassMethod() {
    CompilationUnit cu = parseSample("AnonymousClassDeclarations");
    ClassOrInterfaceDeclaration aClass = Navigator.demandClass(cu, "AnonymousClassDeclarations");
    MethodDeclaration method = Navigator.demandMethod(aClass, "fooBar2");
    MethodCallExpr methodCall = Navigator.findMethodCall(method, "innerClassMethod").get();

    CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
    combinedTypeSolver.add(new ReflectionTypeSolver());
    MethodUsage methodUsage =
        JavaParserFacade.get(combinedTypeSolver).solveMethodAsUsage(methodCall);

    assertThat(methodUsage.getQualifiedSignature(),
               is("AnonymousClassDeclarations.DoFn.ProcessContext.innerClassMethod()"));
  }

  @Test
  void callingAnonymousClassInnerMethod() {
    CompilationUnit cu = parseSample("AnonymousClassDeclarations");
    ClassOrInterfaceDeclaration aClass = Navigator.demandClass(cu, "AnonymousClassDeclarations");
    MethodDeclaration method = Navigator.demandMethod(aClass, "fooBar3");
    MethodCallExpr methodCall = Navigator.findMethodCall(method, "callAnnonClassInnerMethod").get();

    CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
    combinedTypeSolver.add(new ReflectionTypeSolver());
    MethodUsage methodUsage =
        JavaParserFacade.get(combinedTypeSolver).solveMethodAsUsage(methodCall);

    assertTrue(methodUsage.getQualifiedSignature().startsWith("AnonymousClassDeclarations"));
    assertTrue(methodUsage.getQualifiedSignature().contains("Anonymous-"));
    assertTrue(methodUsage.getQualifiedSignature().endsWith("callAnnonClassInnerMethod()"));
  }

  @Test
  void usingAnonymousSuperClassInnerType() {
    CompilationUnit cu = parseSample("AnonymousClassDeclarations");
    ClassOrInterfaceDeclaration aClass = Navigator.demandClass(cu, "AnonymousClassDeclarations");
    MethodDeclaration method = Navigator.demandMethod(aClass, "fooBar4");
    MethodCallExpr methodCall = Navigator.findMethodCall(method, "toString").get();

    CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
    combinedTypeSolver.add(new ReflectionTypeSolver());
    MethodUsage methodUsage =
        JavaParserFacade.get(combinedTypeSolver).solveMethodAsUsage(methodCall);

    assertThat(methodUsage.getQualifiedSignature(), is("java.lang.Enum.toString()"));
  }

  @Test
  void usingAnonymousClassInnerType() {
    CompilationUnit cu = parseSample("AnonymousClassDeclarations");
    ClassOrInterfaceDeclaration aClass = Navigator.demandClass(cu, "AnonymousClassDeclarations");
    MethodDeclaration method = Navigator.demandMethod(aClass, "fooBar5");
    MethodCallExpr methodCall = Navigator.findMethodCall(method, "toString").get();

    CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
    combinedTypeSolver.add(new ReflectionTypeSolver());
    MethodUsage methodUsage =
        JavaParserFacade.get(combinedTypeSolver).solveMethodAsUsage(methodCall);

    assertThat(methodUsage.getQualifiedSignature(), is("java.lang.Enum.toString()"));
  }

  @Test
  void callingScopedAnonymousClassInnerMethod() {
    CompilationUnit cu = parseSample("AnonymousClassDeclarations");
    ClassOrInterfaceDeclaration aClass = Navigator.demandClass(cu, "AnonymousClassDeclarations");
    MethodDeclaration method = Navigator.demandMethod(aClass, "fooBar6");
    MethodCallExpr methodCall = Navigator.findMethodCall(method, "innerClassMethod").get();

    CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
    combinedTypeSolver.add(new ReflectionTypeSolver());
    MethodUsage methodUsage =
            JavaParserFacade.get(combinedTypeSolver).solveMethodAsUsage(methodCall);

    assertThat(methodUsage.getQualifiedSignature(), is("AnonymousClassDeclarations.DoFn.ProcessContext.innerClassMethod()"));
  }
}
