/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.logic.ConfilictingGenericTypesException;
import com.github.javaparser.symbolsolver.logic.InferenceContext;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class ReflectionEnumDeclaration extends AbstractTypeDeclaration implements ResolvedEnumDeclaration {

  ///
  /// Fields
  ///

  private Class<?> clazz;
  private TypeSolver typeSolver;
  private ReflectionClassAdapter reflectionClassAdapter;

  ///
  /// Constructors
  ///

  public ReflectionEnumDeclaration(Class<?> clazz, TypeSolver typeSolver) {
    if (clazz == null) {
      throw new IllegalArgumentException("Class should not be null");
    }
    if (clazz.isInterface()) {
      throw new IllegalArgumentException("Class should not be an interface");
    }
    if (clazz.isPrimitive()) {
      throw new IllegalArgumentException("Class should not represent a primitive class");
    }
    if (clazz.isArray()) {
      throw new IllegalArgumentException("Class should not be an array");
    }
    if (!clazz.isEnum()) {
      throw new IllegalArgumentException("Class should be an enum");
    }
    this.clazz = clazz;
    this.typeSolver = typeSolver;
    this.reflectionClassAdapter = new ReflectionClassAdapter(clazz, typeSolver, this);
  }

  ///
  /// Public methods
  ///

  @Override
  public AccessSpecifier accessSpecifier() {
    return ReflectionFactory.modifiersToAccessLevel(this.clazz.getModifiers());
  }
  
  @Override
  public Optional<ResolvedReferenceTypeDeclaration> containerType() {
      return reflectionClassAdapter.containerType();
  }

  @Override
  public String getPackageName() {
    if (clazz.getPackage() != null) {
      return clazz.getPackage().getName();
    }
    return null;
  }

  @Override
  public String getClassName() {
    String canonicalName = clazz.getCanonicalName();
    if (canonicalName != null && getPackageName() != null) {
      return canonicalName.substring(getPackageName().length() + 1, canonicalName.length());
    }
    return null;
  }

  @Override
  public String getQualifiedName() {
    return clazz.getCanonicalName();
  }

  @Override
  public List<ResolvedReferenceType> getAncestors() {
    return reflectionClassAdapter.getAncestors();
  }

  @Override
  public ResolvedFieldDeclaration getField(String name) {
    return reflectionClassAdapter.getField(name);
  }

  @Override
  public boolean hasField(String name) {
    return reflectionClassAdapter.hasField(name);
  }

  @Override
  public List<ResolvedFieldDeclaration> getAllFields() {
    return reflectionClassAdapter.getAllFields();
  }

  @Override
  public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
    return reflectionClassAdapter.getDeclaredMethods();
  }

  @Override
  public boolean isAssignableBy(ResolvedType type) {
    return reflectionClassAdapter.isAssignableBy(type);
  }

  @Override
  public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
    return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
  }

  @Override
  public boolean hasDirectlyAnnotation(String qualifiedName) {
    return reflectionClassAdapter.hasDirectlyAnnotation(qualifiedName);
  }

  @Override
  public String getName() {
    return clazz.getSimpleName();
  }

  @Override
  public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
    return reflectionClassAdapter.getTypeParameters();
  }

  public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> parameterTypes, boolean staticOnly) {
    return ReflectionMethodResolutionLogic.solveMethod(name, parameterTypes, staticOnly,
            typeSolver,this, clazz);
  }

  public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> parameterTypes, TypeSolver typeSolver,
                                                  Context invokationContext, List<ResolvedType> typeParameterValues) {
    Optional<MethodUsage> res = ReflectionMethodResolutionLogic.solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext,
            typeParameterValues, this, clazz);
    if (res.isPresent()) {
        // We have to replace method type typeParametersValues here
        InferenceContext inferenceContext = new InferenceContext(MyObjectProvider.INSTANCE);
        MethodUsage methodUsage = res.get();
        int i = 0;
        List<ResolvedType> parameters = new LinkedList<>();
        for (ResolvedType actualType : parameterTypes) {
          ResolvedType formalType = methodUsage.getParamType(i);
            // We need to replace the class type typeParametersValues (while we derive the method ones)

            parameters.add(inferenceContext.addPair(formalType, actualType));
            i++;
        }
        try {
          ResolvedType returnType = inferenceContext.addSingle(methodUsage.returnType());
            for (int j=0;j<parameters.size();j++) {
                methodUsage = methodUsage.replaceParamType(j, inferenceContext.resolve(parameters.get(j)));
            }
            methodUsage = methodUsage.replaceReturnType(inferenceContext.resolve(returnType));
            return Optional.of(methodUsage);
        } catch (ConfilictingGenericTypesException e) {
            return Optional.empty();
        }
    } else {
        return res;
    }
}

  @Override
  public List<ResolvedEnumConstantDeclaration> getEnumConstants() {
      return Arrays.stream(clazz.getFields())
              .filter(f -> f.isEnumConstant())
              .map(c -> new ReflectionEnumConstantDeclaration(c, typeSolver))
              .collect(Collectors.toList());
  }
}
