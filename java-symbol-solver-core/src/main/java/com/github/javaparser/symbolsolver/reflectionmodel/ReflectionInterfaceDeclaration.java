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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.logic.ConfilictingGenericTypesException;
import com.github.javaparser.symbolsolver.logic.GenericTypeInferenceLogic;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.NullType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import javaslang.Tuple2;

import java.lang.annotation.Annotation;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.TypeVariable;
import java.util.*;
import java.util.stream.Collectors;

public class ReflectionInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {

    private Class<?> clazz;
    private TypeSolver typeSolver;

    public ReflectionInterfaceDeclaration(Class<?> clazz, TypeSolver typeSolver) {
        if (!clazz.isInterface()) {
            throw new IllegalArgumentException();
        }

        this.clazz = clazz;
        this.typeSolver = typeSolver;
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    @Override
    public String getQualifiedName() {
        return clazz.getCanonicalName();
    }

    public Context getContext() {
        return new ClassOrInterfaceDeclarationContext(clazz);
    }

    @Deprecated
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes) {
        List<MethodDeclaration> methods = new ArrayList<>();
        for (Method method : clazz.getMethods()) {
            if (method.isBridge() || method.isSynthetic()) continue;
            MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            methods.add(methodDeclaration);
        }
        return MethodResolutionLogic.findMostApplicable(methods, name, parameterTypes, typeSolver);
    }

    @Override
    public String toString() {
        return "ReflectionClassDeclaration{" +
                "clazz=" + clazz.getCanonicalName() +
                '}';
    }

    public Type getUsage(Node node) {
        return new ReferenceTypeImpl(this, typeSolver);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ReflectionInterfaceDeclaration)) return false;

        ReflectionInterfaceDeclaration that = (ReflectionInterfaceDeclaration) o;

        if (!clazz.getCanonicalName().equals(that.clazz.getCanonicalName())) return false;

        if (!getTypeParameters().equals(that.getTypeParameters())) {
            return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        return clazz.hashCode();
    }

    public Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> parameterTypes, TypeSolver typeSolver, Context invokationContext, List<Type> typeParameterValues) {
        Optional<MethodUsage> res = ReflectionMethodResolutionLogic.solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext,
                typeParameterValues, this, clazz);
        if (res.isPresent()) {
            // We have to replace method type typeParametersValues here
            List<Tuple2<Type, Type>> formalActualTypePairs = new ArrayList<>();
            MethodUsage methodUsage = res.get();
            int i = 0;
            for (Type actualType : parameterTypes) {
                Type formalType = methodUsage.getParamType(i);
                // We need to replace the class type typeParametersValues (while we derive the method ones)

                formalActualTypePairs.add(new Tuple2<>(formalType, actualType));
                i++;
            }
            try {
                Map<TypeParameterDeclaration, Type> map = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
                for (TypeParameterDeclaration key : map.keySet()) {
                    if (map.get(key) == null) {
                        throw new IllegalArgumentException();
                    }
                    methodUsage = methodUsage.replaceTypeParameter(key, map.get(key));
                }
                return Optional.of(methodUsage);
            } catch (ConfilictingGenericTypesException e) {
                return Optional.empty();
            }
        } else {
            return res;
        }
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other) {
        if (other instanceof LambdaArgumentTypePlaceholder) {
            return isFunctionalInterface();
        }
        if (other.getQualifiedName().equals(getQualifiedName())) {
            return true;
        }
        if (this.clazz.getSuperclass() != null
                && new ReflectionInterfaceDeclaration(clazz.getSuperclass(), typeSolver).canBeAssignedTo(other)) {
            return true;
        }
        for (Class interfaze : clazz.getInterfaces()) {
            if (new ReflectionInterfaceDeclaration(interfaze, typeSolver).canBeAssignedTo(other)) {
                return true;
            }
        }

        if (other.getQualifiedName().equals(Object.class.getCanonicalName())) {
            return true;
        }

        return false;
    }

    @Override
    public boolean isAssignableBy(Type type) {
        if (type instanceof NullType) {
            return true;
        }
        if (type instanceof LambdaArgumentTypePlaceholder) {
            return isFunctionalInterface();
        }
        if (type.isArray()) {
            return false;
        }
        if (type.isPrimitive()) {
            return false;
        }
        if (type.describe().equals(getQualifiedName())) {
            return true;
        }
        if (type instanceof ReferenceTypeImpl) {
            ReferenceTypeImpl otherTypeDeclaration = (ReferenceTypeImpl) type;
            return otherTypeDeclaration.getTypeDeclaration().canBeAssignedTo(this);
        }

        return false;
    }

    @Override
    public boolean isTypeParameter() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
        for (Field field : clazz.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return new ReflectionFieldDeclaration(field, typeSolver);
            }
        }
        for (ReferenceType ancestor : getAllAncestors()) {
            if (ancestor.getTypeDeclaration().hasField(name)) {
                return ancestor.getTypeDeclaration().getField(name);
            }
        }
        throw new UnsolvedSymbolException("Field in " + this, name);
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        List<FieldDeclaration> fields = new ArrayList<>();
        for (Field field : clazz.getDeclaredFields()) {
            fields.add(new ReflectionFieldDeclaration(field, typeSolver));
        }
        for (ReferenceType ancestor : getAllAncestors()) {
            fields.addAll(ancestor.getTypeDeclaration().getAllFields());
        }
        return fields;
    }

    @Deprecated
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Field field : clazz.getFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new ReflectionFieldDeclaration(field, typeSolver));
            }
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new LinkedList<>();
        if (clazz.getGenericSuperclass() != null) {
            if (clazz.getGenericSuperclass() instanceof ParameterizedType) {
                ParameterizedType parameterizedType = (ParameterizedType) clazz.getGenericSuperclass();
                List<Type> typeParameters = Arrays.stream(parameterizedType.getActualTypeArguments())
                        .map((t) -> ReflectionFactory.typeUsageFor(t, typeSolver))
                        .collect(Collectors.toList());
                ancestors.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class)parameterizedType.getRawType(), typeSolver), typeParameters, typeSolver));
            } else {
                ancestors.add(new ReferenceTypeImpl(new ReflectionClassDeclaration((Class)clazz.getGenericSuperclass(), typeSolver), typeSolver));
            }
        }
        for (java.lang.reflect.Type interfaze : clazz.getGenericInterfaces()) {
            if (interfaze instanceof ParameterizedType) {
                ParameterizedType parameterizedType = (ParameterizedType) interfaze;
                List<Type> typeParameters = Arrays.stream(parameterizedType.getActualTypeArguments())
                        .map((t) -> ReflectionFactory.typeUsageFor(t, typeSolver))
                        .collect(Collectors.toList());
                ancestors.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class)parameterizedType.getRawType(), typeSolver), typeParameters, typeSolver));
            } else {
                ancestors.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class)interfaze, typeSolver), typeSolver));
            }
        }
        for (int i = 0; i < ancestors.size(); i++) {
            if (ancestors.get(i).getQualifiedName().equals(Object.class.getCanonicalName())) {
                ancestors.remove(i);
                i--;
            }
        }
        ReferenceTypeImpl object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        ancestors.add(object);
        return ancestors;
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(clazz.getDeclaredMethods())
                .filter(m -> !m.isSynthetic() && !m.isBridge())
                .map(m -> new ReflectionMethodDeclaration(m, typeSolver))
                .collect(Collectors.toSet());
    }

    @Override
    public boolean hasField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return clazz.getSimpleName();
    }

    @Override
    public boolean isInterface() {
        return true;
    }

    @Override
    public List<ReferenceType> getInterfacesExtended() {
        List<ReferenceType> res = new ArrayList<>();
        for (Class i : clazz.getInterfaces()) {
            res.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(i, typeSolver), typeSolver));
        }
        return res;
    }

    @Override
    public InterfaceDeclaration asInterface() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        for (Annotation a : clazz.getDeclaredAnnotations()) {
            if (a.annotationType().getCanonicalName().equals(canonicalName)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        List<TypeParameterDeclaration> params = new ArrayList<>();
        for (TypeVariable tv : this.clazz.getTypeParameters()) {
            params.add(new ReflectionTypeParameter(tv, true, typeSolver));
        }
        return params;
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }
}
