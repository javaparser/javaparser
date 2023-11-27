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

package com.github.javaparser.symbolsolver.resolution.typeinference.bounds;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedWildcard;
import com.github.javaparser.symbolsolver.resolution.typeinference.Bound;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariable;
import com.github.javaparser.symbolsolver.resolution.typeinference.ProperLowerBound;
import com.github.javaparser.symbolsolver.resolution.typeinference.ProperUpperBound;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isProperType;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.mock;

class SubtypeOfBoundTest {

    private TypeSolver typeSolver = new ReflectionTypeSolver();
    private ResolvedReferenceType iterableType = new ReferenceTypeImpl(new ReflectionTypeSolver().solveType(Iterable.class.getCanonicalName()));
    private ResolvedReferenceType listType = new ReferenceTypeImpl(new ReflectionTypeSolver().solveType(List.class.getCanonicalName()));
    private ResolvedType integerType = new ReferenceTypeImpl(new ReflectionTypeSolver().solveType(Integer.class.getCanonicalName()));
    private ResolvedType doubleType = new ReferenceTypeImpl(new ReflectionTypeSolver().solveType(Double.class.getCanonicalName()));
    private ResolvedType objectType = new ReferenceTypeImpl(new ReflectionTypeSolver().solveType(Object.class.getCanonicalName()));

    @Test
    void recognizeProperLowerBound1() {
        ResolvedTypeParameterDeclaration typeParameterDeclaration = mock(ResolvedTypeParameterDeclaration.class);

        // { Integer <: α, Double <: α, α <: Object } describes two proper lower bounds and one proper upper bound for α.

        InferenceVariable inferenceVariable = new InferenceVariable("α", typeParameterDeclaration);
        Bound bound = new SubtypeOfBound(integerType, inferenceVariable);

        assertEquals(Optional.of(new ProperLowerBound(inferenceVariable, integerType)), bound.isProperLowerBound());
    }

    @Test
    void recognizeProperLowerBound2() {
        ResolvedTypeParameterDeclaration typeParameterDeclaration = mock(ResolvedTypeParameterDeclaration.class);

        // { Integer <: α, Double <: α, α <: Object } describes two proper lower bounds and one proper upper bound for α.

        InferenceVariable inferenceVariable = new InferenceVariable("α", typeParameterDeclaration);
        Bound bound = new SubtypeOfBound(doubleType, inferenceVariable);

        assertEquals(Optional.of(new ProperLowerBound(inferenceVariable, doubleType)), bound.isProperLowerBound());
    }

    @Test
    void recognizeProperUpperBound1() {
        ResolvedTypeParameterDeclaration typeParameterDeclaration = mock(ResolvedTypeParameterDeclaration.class);

        // { Integer <: α, Double <: α, α <: Object } describes two proper lower bounds and one proper upper bound for α.

        InferenceVariable inferenceVariable = new InferenceVariable("α", typeParameterDeclaration);
        Bound bound = new SubtypeOfBound(inferenceVariable, objectType);

        assertEquals(Optional.of(new ProperUpperBound(inferenceVariable, objectType)), bound.isProperUpperBound());
    }

    @Test
    void recognizeProperUpperBound2() {
        ResolvedTypeParameterDeclaration typeParameterDeclaration1 = mock(ResolvedTypeParameterDeclaration.class);
        ResolvedTypeParameterDeclaration typeParameterDeclaration2 = mock(ResolvedTypeParameterDeclaration.class);
        // { α <: Iterable<?>, β <: Object, α <: List<β> } describes a proper upper bound for each of α and β, along with a dependency between them.

        InferenceVariable alpha = new InferenceVariable("α", typeParameterDeclaration1);
        InferenceVariable beta = new InferenceVariable("β", typeParameterDeclaration2);
        ResolvedType iterableOfWildcard = new ReferenceTypeImpl(iterableType.getTypeDeclaration().get(), Arrays.asList(ResolvedWildcard.UNBOUNDED));
        ResolvedType listOfBeta = new ReferenceTypeImpl(listType.getTypeDeclaration().get(), Arrays.asList(beta));

        Bound bound1 = new SubtypeOfBound(alpha, iterableOfWildcard);
        Bound bound2 = new SubtypeOfBound(beta, objectType);
        Bound bound3 = new SubtypeOfBound(alpha, listOfBeta);

        assertEquals(false, isProperType(listOfBeta));
        assertEquals(Optional.of(new ProperUpperBound(alpha, iterableOfWildcard)), bound1.isProperUpperBound());
        assertEquals(Optional.of(new ProperUpperBound(beta, objectType)), bound2.isProperUpperBound());
        assertEquals(true, bound3.isADependency());
    }
}
