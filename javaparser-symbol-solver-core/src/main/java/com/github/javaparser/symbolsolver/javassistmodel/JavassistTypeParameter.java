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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodLikeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParametrizable;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import javassist.bytecode.SignatureAttribute;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class JavassistTypeParameter implements ResolvedTypeParameterDeclaration {

    private SignatureAttribute.TypeParameter wrapped;
    private TypeSolver typeSolver;
    private ResolvedTypeParametrizable container;

    public JavassistTypeParameter(SignatureAttribute.TypeParameter wrapped, ResolvedTypeParametrizable container, TypeSolver typeSolver) {
        this.wrapped = wrapped;
        this.typeSolver = typeSolver;
        this.container = container;
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
        return Objects.hash(getQualifiedName(), declaredOnType(), declaredOnMethod());
    }

    @Override
    public String toString() {
        return "JavassistTypeParameter{" +
                wrapped.getName()
                + '}';
    }

    @Override
    public String getName() {
        return wrapped.getName();
    }

    @Override
    public String getContainerQualifiedName() {
        if (this.container instanceof ResolvedReferenceTypeDeclaration) {
            return ((ResolvedReferenceTypeDeclaration) this.container).getQualifiedName();
        }
        if (this.container instanceof ResolvedMethodLikeDeclaration) {
            return ((ResolvedMethodLikeDeclaration) this.container).getQualifiedName();
        }
        throw new UnsupportedOperationException();
    }

    @Override
    public String getContainerId() {
        return getContainerQualifiedName();
    }

    @Override
    public ResolvedTypeParametrizable getContainer() {
        return this.container;
    }

    @Override
    public List<ResolvedTypeParameterDeclaration.Bound> getBounds() {
        List<Bound> bounds = new ArrayList<>();
        SignatureAttribute.ObjectType classBound = wrapped.getClassBound();
        if (classBound != null) {
            bounds.add(Bound.extendsBound(JavassistUtils.signatureTypeToType(classBound, typeSolver, getContainer())));
        }
        for (SignatureAttribute.ObjectType ot : wrapped.getInterfaceBound()) {
            bounds.add(Bound.extendsBound(JavassistUtils.signatureTypeToType(ot, typeSolver, getContainer())));
        }
        return bounds;
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
