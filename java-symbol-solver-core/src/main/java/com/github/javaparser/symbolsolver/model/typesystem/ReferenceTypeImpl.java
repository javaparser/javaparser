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

package com.github.javaparser.symbolsolver.model.typesystem;

import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeVariableDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

// TODO Remove references to typeSolver: it is needed to instantiate other instances of ReferenceTypeUsage
//      and to get the Object type declaration
public class ReferenceTypeImpl extends ReferenceType {

    @Override
    protected ReferenceType create(TypeDeclaration typeDeclaration, List<Type> typeParametersCorrected, TypeSolver typeSolver) {
        return new ReferenceTypeImpl(typeDeclaration, typeParametersCorrected, typeSolver);
    }

    @Override
    protected ReferenceType create(TypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        return new ReferenceTypeImpl(typeDeclaration, typeSolver);
    }

    public ReferenceTypeImpl(TypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        super(typeDeclaration, typeSolver);
    }

    public ReferenceTypeImpl(TypeDeclaration typeDeclaration, List<Type> typeParameters, TypeSolver typeSolver) {
        super(typeDeclaration, typeParameters, typeSolver);
    }

    @Override
    public TypeParameterDeclaration asTypeParameter() {
        if (this.typeDeclaration instanceof JavaParserTypeVariableDeclaration) {
            JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration) this.typeDeclaration;
            return javaParserTypeVariableDeclaration.asTypeParameter();
        }
        throw new UnsupportedOperationException(this.typeDeclaration.getClass().getCanonicalName());
    }

    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    @Override
    public boolean isAssignableBy(Type other) {
        if (other instanceof NullType) {
            return !this.isPrimitive();
        }
        // consider boxing
        if (other.isPrimitive()) {
            if (this.getQualifiedName().equals(Object.class.getCanonicalName())) {
                return true;
            } else {
                return isCorrespondingBoxingType(other.describe());
            }
        }
        if (other instanceof LambdaArgumentTypePlaceholder) {
            return this.getTypeDeclaration().hasAnnotation(FunctionalInterface.class.getCanonicalName());
        } else if (other instanceof ReferenceTypeImpl) {
            ReferenceTypeImpl otherRef = (ReferenceTypeImpl) other;
            if (compareConsideringTypeParameters(otherRef)) {
                return true;
            }
            for (ReferenceType otherAncestor : otherRef.getAllAncestors()) {
                if (compareConsideringTypeParameters(otherAncestor)) {
                    return true;
                }
            }
            return false;
        } else if (other.isTypeVariable()) {
            // TODO look bounds...
            return true;
        } else if (other.isWildcard()) {
            if (this.getQualifiedName().equals(Object.class.getCanonicalName())) {
                return true;
            } else if (other.asWildcard().isExtends()) {
                return isAssignableBy(other.asWildcard().getBoundedType());
            } else {
                return false;
            }
        } else {
            return false;
        }
    }

    @Override
    public Set<MethodUsage> getDeclaredMethods() {
        // TODO replace variables
        Set<MethodUsage> methods = new HashSet<>();
        for (MethodDeclaration methodDeclaration : getTypeDeclaration().getDeclaredMethods()) {
            MethodUsage methodUsage = new MethodUsage(methodDeclaration);
            methods.add(methodUsage);
        }
        return methods;
    }


}
