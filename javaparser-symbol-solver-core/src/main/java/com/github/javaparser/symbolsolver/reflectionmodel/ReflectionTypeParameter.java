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

import com.github.javaparser.resolution.declarations.ResolvedMethodLikeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParametrizable;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.Constructor;
import java.lang.reflect.GenericDeclaration;
import java.lang.reflect.Method;
import java.lang.reflect.TypeVariable;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class ReflectionTypeParameter implements ResolvedTypeParameterDeclaration {

    private TypeVariable typeVariable;
    private TypeSolver typeSolver;
    private ResolvedTypeParametrizable container;

    public ReflectionTypeParameter(TypeVariable typeVariable, boolean declaredOnClass, TypeSolver typeSolver) {
        GenericDeclaration genericDeclaration = typeVariable.getGenericDeclaration();
        if (genericDeclaration instanceof Class) {
            container = ReflectionFactory.typeDeclarationFor((Class) genericDeclaration, typeSolver);
        } else if (genericDeclaration instanceof Method) {
            container = new ReflectionMethodDeclaration((Method) genericDeclaration, typeSolver);
        } else if (genericDeclaration instanceof Constructor) {
            container = new ReflectionConstructorDeclaration((Constructor) genericDeclaration, typeSolver);
        }
        this.typeVariable = typeVariable;
        this.typeSolver = typeSolver;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ResolvedTypeParameterDeclaration)) return false;

        ResolvedTypeParameterDeclaration that = (ResolvedTypeParameterDeclaration) o;

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
        result = 31 * result + container.hashCode();
        return result;
    }

    @Override
    public String getName() {
        return typeVariable.getName();
    }

    @Override
    public String getContainerQualifiedName() {
        if (container instanceof ResolvedReferenceTypeDeclaration) {
            return ((ResolvedReferenceTypeDeclaration) container).getQualifiedName();
        } else {
            return ((ResolvedMethodLikeDeclaration) container).getQualifiedSignature();
        }
    }

    @Override
    public String getContainerId() {
        if (container instanceof ResolvedReferenceTypeDeclaration) {
            return ((ResolvedReferenceTypeDeclaration) container).getId();
        } else {
            return ((ResolvedMethodLikeDeclaration) container).getQualifiedSignature();
        }
    }
    
    @Override
    public ResolvedTypeParametrizable getContainer() {
        return this.container;
    }

    @Override
    public List<Bound> getBounds() {
        return Arrays.stream(typeVariable.getBounds()).map((refB) -> Bound.extendsBound(ReflectionFactory.typeUsageFor(refB, typeSolver))).collect(Collectors.toList());
    }

    @Override
    public String toString() {
        return "ReflectionTypeParameter{" +
                "typeVariable=" + typeVariable +
                '}';
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        if (container instanceof ResolvedReferenceTypeDeclaration) {
            return Optional.of((ResolvedReferenceTypeDeclaration) container);
        }
        return Optional.empty();
    }
}
