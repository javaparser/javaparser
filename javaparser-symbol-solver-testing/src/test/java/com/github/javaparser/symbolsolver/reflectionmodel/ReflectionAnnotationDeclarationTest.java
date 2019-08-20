package com.github.javaparser.symbolsolver.reflectionmodel;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Collections;
import java.util.stream.Collectors;
import org.junit.jupiter.api.Test;

@interface OuterAnnotation {
  @interface InnerAnnotation {}
}

@interface WithValue {
  String value();
}

class ReflectionAnnotationDeclarationTest {
  private TypeSolver typeSolver = new ReflectionTypeSolver(false);

  @Test
  void isClass() {
    ReflectionAnnotationDeclaration
        annotation = (ReflectionAnnotationDeclaration) typeSolver.solveType(
            "com.github.javaparser.symbolsolver.reflectionmodel.OuterAnnotation");
    assertFalse(annotation.isClass());
  }

  @Test
  void innerIsClass() {
    ReflectionAnnotationDeclaration
        annotation = (ReflectionAnnotationDeclaration) typeSolver.solveType(
            "com.github.javaparser.symbolsolver.reflectionmodel.OuterAnnotation.InnerAnnotation");
    assertFalse(annotation.isClass());
  }

  @Test
  void getInternalTypes() {
    ReflectionAnnotationDeclaration annotation =
        (ReflectionAnnotationDeclaration) typeSolver.solveType(
            "com.github.javaparser.symbolsolver.reflectionmodel.OuterAnnotation");
    assertEquals(Collections.singleton("InnerAnnotation"),
        annotation.internalTypes().stream().map(ResolvedDeclaration::getName).collect(Collectors.toSet()));
  }

  @Test
  void solveMethodForAnnotationWithValue() {
    ReflectionAnnotationDeclaration annotation =
        (ReflectionAnnotationDeclaration) typeSolver.solveType(WithValue.class.getCanonicalName());
    final SymbolReference<ResolvedMethodDeclaration> symbolReference =
        annotation.solveMethod("value", Collections.emptyList(), false);
    assertEquals("value", symbolReference.getCorrespondingDeclaration().getName());
  }
}
