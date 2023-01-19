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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.lang.annotation.Inherited;
import java.util.Collections;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.*;

@interface OuterAnnotation {
  @interface InnerAnnotation {}
}

@interface WithValue {
  String value();
}

@interface WithField {
  int FIELD_DECLARATION = 0;
}

@Inherited
@interface InheritedAnnotation {}

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

  @Test
  void getAllFields_shouldReturnTheCorrectFields() {
    ReflectionAnnotationDeclaration annotation =
            (ReflectionAnnotationDeclaration) typeSolver.solveType(
                    "com.github.javaparser.symbolsolver.reflectionmodel.WithField");
    assertEquals(Collections.singleton("FIELD_DECLARATION"),
            annotation.getAllFields().stream().map(ResolvedDeclaration::getName).collect(Collectors.toSet()));
  }
  
  @Test
  void getClassName_shouldReturnCorrectValue() {
    ReflectionAnnotationDeclaration annotation =
        (ReflectionAnnotationDeclaration) typeSolver.solveType(
            "com.github.javaparser.symbolsolver.reflectionmodel.WithField");
    assertEquals("WithField", annotation.getClassName());
  }
  
  @Test
  void isAnnotationNotInheritable() {
    ReflectionAnnotationDeclaration
        annotation = (ReflectionAnnotationDeclaration) typeSolver.solveType(
            "com.github.javaparser.symbolsolver.reflectionmodel.OuterAnnotation");
    assertFalse(annotation.isInheritable());
  }
  
  @Test
  void isAnnotationInheritable() {
    ReflectionAnnotationDeclaration
        annotation = (ReflectionAnnotationDeclaration) typeSolver.solveType(
            "com.github.javaparser.symbolsolver.reflectionmodel.InheritedAnnotation");
    assertTrue(annotation.isInheritable());
  }

}
