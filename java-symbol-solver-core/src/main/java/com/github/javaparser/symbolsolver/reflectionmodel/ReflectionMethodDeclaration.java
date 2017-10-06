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

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.declarations.common.MethodDeclarationCommonLogic;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class ReflectionMethodDeclaration implements ResolvedMethodDeclaration {

    private Method method;
    private TypeSolver typeSolver;

    public ReflectionMethodDeclaration(Method method, TypeSolver typeSolver) {
        this.method = method;
        if (method.isSynthetic() || method.isBridge()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        return method.getName();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public String toString() {
        return "ReflectionMethodDeclaration{" +
                "method=" + method +
                '}';
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public ResolvedReferenceTypeDeclaration declaringType() {
        if (method.getDeclaringClass().isInterface()) {
            return new ReflectionInterfaceDeclaration(method.getDeclaringClass(), typeSolver);
        }
        if (method.getDeclaringClass().isEnum()) {
            return new ReflectionEnumDeclaration(method.getDeclaringClass(), typeSolver);
        } else {
            return new ReflectionClassDeclaration(method.getDeclaringClass(), typeSolver);
        }
    }

    @Override
    public ResolvedType getReturnType() {
        return ReflectionFactory.typeUsageFor(method.getGenericReturnType(), typeSolver);
    }

    @Override
    public int getNumberOfParams() {
        return method.getParameterTypes().length;
    }

    @Override
    public ResolvedParameterDeclaration getParam(int i) {
        boolean variadic = false;
        if (method.isVarArgs()) {
            variadic = i == (method.getParameterCount() - 1);
        }
        return new ReflectionParameterDeclaration(method.getParameterTypes()[i], method.getGenericParameterTypes()[i], typeSolver, variadic);
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return Arrays.stream(method.getTypeParameters()).map((refTp) -> new ReflectionTypeParameter(refTp, false, typeSolver)).collect(Collectors.toList());
    }

    public MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes) {
        return new MethodDeclarationCommonLogic(this, typeSolver).resolveTypeVariables(context, parameterTypes);
    }

    @Override
    public boolean isAbstract() {
        return Modifier.isAbstract(method.getModifiers());
    }

    @Override
    public boolean isDefaultMethod() {
        return method.isDefault();
    }

    @Override
    public boolean isStatic() {
        return Modifier.isStatic(method.getModifiers());
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return ReflectionFactory.modifiersToAccessLevel(this.method.getModifiers());
    }

    @Override
    public int getNumberOfSpecifiedExceptions() {
        return this.method.getExceptionTypes().length;
    }

    @Override
    public ResolvedType getSpecifiedException(int index) {
        if (index < 0 || index >= getNumberOfSpecifiedExceptions()) {
            throw new IllegalArgumentException();
        }
        return ReflectionFactory.typeUsageFor(this.method.getExceptionTypes()[index], typeSolver);
    }
}
