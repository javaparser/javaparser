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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import javassist.bytecode.SignatureAttribute;

import java.util.ArrayList;
import java.util.List;
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
        } else if (this.container instanceof ResolvedMethodLikeDeclaration) {
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
        if (wrapped.getClassBound() != null && !wrapped.getClassBound().toString().equals(Object.class.getCanonicalName())) {
            throw new UnsupportedOperationException(wrapped.getClassBound().toString());
        }
        for (SignatureAttribute.ObjectType ot : wrapped.getInterfaceBound()) {
            throw new UnsupportedOperationException(ot.toString());
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
}
