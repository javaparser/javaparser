package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import static org.hamcrest.core.Is.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.jupiter.api.Assertions.assertTrue;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

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

    assertThat(methodUsage.getQualifiedSignature(),
               is("AnonymousClassDeclarations.ParDo.of(AnonymousClassDeclarations.DoFn<I, O>)"));
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
