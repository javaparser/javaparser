/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.model.typesystem;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeTransformer;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeVariableDeclaration;
import com.github.javaparser.symbolsolver.logic.FunctionalInterfaceLogic;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
// TODO Remove references to typeSolver: it is needed to instantiate other instances of ReferenceTypeUsage
//      and to get the Object type declaration
public class ReferenceTypeImpl extends ResolvedReferenceType {

    private TypeSolver typeSolver;

    public static ResolvedReferenceType undeterminedParameters(ResolvedReferenceTypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        return new ReferenceTypeImpl(typeDeclaration, typeDeclaration.getTypeParameters().stream().map(
                ResolvedTypeVariable::new
        ).collect(Collectors.toList()), typeSolver);
    }

    @Override
    protected ResolvedReferenceType create(ResolvedReferenceTypeDeclaration typeDeclaration, List<ResolvedType> typeParametersCorrected) {
        return new ReferenceTypeImpl(typeDeclaration, typeParametersCorrected, typeSolver);
    }

    @Override
    protected ResolvedReferenceType create(ResolvedReferenceTypeDeclaration typeDeclaration) {
        return new ReferenceTypeImpl(typeDeclaration, typeSolver);
    }

    public ReferenceTypeImpl(ResolvedReferenceTypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        super(typeDeclaration);
        this.typeSolver = typeSolver;
    }

    public ReferenceTypeImpl(ResolvedReferenceTypeDeclaration typeDeclaration, List<ResolvedType> typeArguments, TypeSolver typeSolver) {
        super(typeDeclaration, typeArguments);
        this.typeSolver = typeSolver;
    }

    @Override
    public ResolvedTypeParameterDeclaration asTypeParameter() {
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
    public boolean isAssignableBy(ResolvedType other) {
        if (other instanceof NullType) {
            return !this.isPrimitive();
        }
        // everything is assignable to Object except void
        if (!other.isVoid() && this.getQualifiedName().equals(Object.class.getCanonicalName())) {
            return true;
        }
        // consider boxing
        if (other.isPrimitive()) {
            if (this.getQualifiedName().equals(Object.class.getCanonicalName())) {
                return true;
            } else {
                // Check if 'other' can be boxed to match this type
                if (isCorrespondingBoxingType(other.describe())) return true;

                // Resolve the boxed type and check if it can be assigned via widening reference conversion
                SymbolReference<ResolvedReferenceTypeDeclaration> type = typeSolver.tryToSolveType(other.asPrimitive().getBoxTypeQName());
                return type.getCorrespondingDeclaration().canBeAssignedTo(super.typeDeclaration);
            }
        }
        if (other instanceof LambdaArgumentTypePlaceholder) {
            return FunctionalInterfaceLogic.isFunctionalInterfaceType(this);
        } else if (other instanceof ReferenceTypeImpl) {
            ReferenceTypeImpl otherRef = (ReferenceTypeImpl) other;
            if (compareConsideringTypeParameters(otherRef)) {
                return true;
            }
            for (ResolvedReferenceType otherAncestor : otherRef.getAllAncestors()) {
                if (compareConsideringTypeParameters(otherAncestor)) {
                    return true;
                }
            }
            return false;
        } else if (other.isTypeVariable()) {
            for (ResolvedTypeParameterDeclaration.Bound bound : other.asTypeVariable().asTypeParameter().getBounds()) {
                if (bound.isExtends()) {
                    if (this.isAssignableBy(bound.getType())) {
                        return true;
                    }
                }
            }
            return false;
        } else if (other.isConstraint()){
            return isAssignableBy(other.asConstraintType().getBound());
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
        for (ResolvedMethodDeclaration methodDeclaration : getTypeDeclaration().getDeclaredMethods()) {
            MethodUsage methodUsage = new MethodUsage(methodDeclaration);
            methods.add(methodUsage);
        }
        return methods;
    }

    @Override
    public ResolvedType toRawType() {
        if (this.isRawType()) {
                return this;
        } else {
            return new ReferenceTypeImpl(typeDeclaration, typeSolver);
        }
    }

    @Override
    public boolean mention(List<ResolvedTypeParameterDeclaration> typeParameters) {
        return typeParametersValues().stream().anyMatch(tp -> tp.mention(typeParameters));
    }

    /**
     * Execute a transformation on all the type parameters of this element.
     */
    @Override
    public ResolvedType transformTypeParameters(ResolvedTypeTransformer transformer) {
        ResolvedType result = this;
        int i = 0;
        for (ResolvedType tp : this.typeParametersValues()) {
            ResolvedType transformedTp = transformer.transform(tp);
            // Identity comparison on purpose
            if (transformedTp != tp) {
                List<ResolvedType> typeParametersCorrected = result.asReferenceType().typeParametersValues();
                typeParametersCorrected.set(i, transformedTp);
                result = create(typeDeclaration, typeParametersCorrected);
            }
            i++;
        }
        return result;
    }

    public List<ResolvedReferenceType> getAllAncestors() {
        // We need to go through the inheritance line and propagate the type parametes

        List<ResolvedReferenceType> ancestors = typeDeclaration.getAllAncestors();

        ancestors = ancestors.stream()
                .map(a -> typeParametersMap().replaceAll(a).asReferenceType())
                .collect(Collectors.toList());

        // Avoid repetitions of Object
        ancestors.removeIf(a -> a.getQualifiedName().equals(Object.class.getCanonicalName()));
        ResolvedReferenceTypeDeclaration objectType = typeSolver.solveType(Object.class.getCanonicalName());
        ResolvedReferenceType objectRef = create(objectType);
        ancestors.add(objectRef);
        return ancestors;
    }

    public List<ResolvedReferenceType> getDirectAncestors() {
        // We need to go through the inheritance line and propagate the type parametes

        List<ResolvedReferenceType> ancestors = typeDeclaration.getAncestors();

        ancestors = ancestors.stream()
                .map(a -> typeParametersMap().replaceAll(a).asReferenceType())
                .collect(Collectors.toList());

        // Avoid repetitions of Object
        ancestors.removeIf(a -> a.getQualifiedName().equals(Object.class.getCanonicalName()));
        boolean isClassWithSuperClassOrObject = this.getTypeDeclaration().isClass()
                && (this.getTypeDeclaration().asClass().getSuperClass() == null ||
                        !this.getTypeDeclaration().asClass().getSuperClass().getQualifiedName().equals(Object.class.getCanonicalName())
                || this.getTypeDeclaration().asClass().getQualifiedName().equals(Object.class.getCanonicalName()));
        if (!isClassWithSuperClassOrObject) {
            ResolvedReferenceTypeDeclaration objectType = typeSolver.solveType(Object.class.getCanonicalName());
            ResolvedReferenceType objectRef = create(objectType);
            ancestors.add(objectRef);
        }
        return ancestors;
    }

    public ResolvedReferenceType deriveTypeParameters(ResolvedTypeParametersMap typeParametersMap) {
        return create(typeDeclaration, typeParametersMap);
    }

    @Override
    public Set<ResolvedFieldDeclaration> getDeclaredFields() {
        return new HashSet<>(getTypeDeclaration().getDeclaredFields());
    }
}
