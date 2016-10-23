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

import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.GenericDeclaration;
import java.lang.reflect.Method;
import java.lang.reflect.TypeVariable;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class ReflectionTypeParameter implements TypeParameterDeclaration {

    private TypeVariable typeVariable;
    private boolean declaredOnClass;
    private String qNameOfDeclaringClass;
    private String idOfDeclaringClass;
    private TypeSolver typeSolver;

    public ReflectionTypeParameter(TypeVariable typeVariable, boolean declaredOnClass, TypeSolver typeSolver) {
        GenericDeclaration genericDeclaration = typeVariable.getGenericDeclaration();
        if (genericDeclaration instanceof Class) {
            TypeDeclaration typeDeclaration = ReflectionFactory.typeDeclarationFor((Class) genericDeclaration, typeSolver);
            qNameOfDeclaringClass = typeDeclaration.getQualifiedName();
            idOfDeclaringClass = typeDeclaration.getId();
        } else {
            qNameOfDeclaringClass = null;
            idOfDeclaringClass = null;
        }
        this.typeVariable = typeVariable;
        this.declaredOnClass = declaredOnClass;
        this.typeSolver = typeSolver;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TypeParameterDeclaration)) return false;

        TypeParameterDeclaration that = (TypeParameterDeclaration) o;

        if (!getQualifiedName().equals(that.getQualifiedName())) {
            return false;
        }
        if (declaredOnType() != that.declaredOnType()) {
            return false;
        }
        if (declaredOnMethod() != that.declaredOnMethod()) {
            return false;
        }
        // TODO check bounds
        return true;
    }

    @Override
    public int hashCode() {
        int result = typeVariable.hashCode();
        result = 31 * result + (declaredOnClass ? 1 : 0);
        return result;
    }

    @Override
    public String getName() {
        return typeVariable.getName();
    }

    @Override
    public boolean declaredOnType() {
        return declaredOnClass;
    }

    @Override
    public boolean declaredOnMethod() {
        return !declaredOnClass;
    }

    @Override
    public String getContainerQualifiedName() {
        if (this.declaredOnType()) {
            return qNameOfDeclaringClass;
        } else {
            String qNameContainer = new ReflectionMethodDeclaration((Method)typeVariable.getGenericDeclaration(), typeSolver).getQualifiedSignature();
            return qNameContainer;
        }
    }

    @Override
    public String getContainerId() {
        if (this.declaredOnType()) {
            return idOfDeclaringClass;
        } else {
            String qNameContainer = new ReflectionMethodDeclaration((Method)typeVariable.getGenericDeclaration(), typeSolver).getQualifiedSignature();
            return qNameContainer;
        }
    }

    @Override
    public List<Bound> getBounds(TypeSolver typeSolver) {
        return Arrays.stream(typeVariable.getBounds()).map((refB) -> Bound.extendsBound(ReflectionFactory.typeUsageFor(refB, typeSolver))).collect(Collectors.toList());
    }

    @Override
    public String toString() {
        return "ReflectionTypeParameter{" +
                "typeVariable=" + typeVariable +
                '}';
    }
}
