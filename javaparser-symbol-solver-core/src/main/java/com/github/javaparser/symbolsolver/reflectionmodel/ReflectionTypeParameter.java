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
import com.github.javaparser.resolution.declarations.ResolvedMethodLikeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParametrizable;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;

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
        }
        return ((ResolvedMethodLikeDeclaration) container).getQualifiedSignature();
    }

    @Override
    public String getContainerId() {
        if (container instanceof ResolvedReferenceTypeDeclaration) {
            return ((ResolvedReferenceTypeDeclaration) container).getId();
        }
        return ((ResolvedMethodLikeDeclaration) container).getQualifiedSignature();
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
    
    @Override
    public ResolvedReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject());
    }
}
