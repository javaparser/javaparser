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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import java.util.*;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.utils.Pair;

/**
 * The term "type" is used loosely in this chapter to include type-like syntax that contains inference variables.
 *
 * Assertions that involve inference
 * variables are assertions about every proper type that can be produced by replacing each inference variable with
 * a proper type.
 *
 * @author Federico Tomassetti
 */
public class TypeHelper {

    /**
     * The term proper type excludes such "types" that mention inference variables.
     */
    public static boolean isProperType(ResolvedType type) {
        if (type instanceof InferenceVariable) {
            return false;
        }
        if (type instanceof ResolvedReferenceType) {
            ResolvedReferenceType referenceType = (ResolvedReferenceType) type;
            return referenceType.typeParametersValues().stream().allMatch(it -> isProperType(it));
        }
        if (type instanceof LazyType) {
            return type.asReferenceType().typeParametersValues().stream().allMatch(it -> isProperType(it));
        }
        if (type instanceof ResolvedWildcard) {
            ResolvedWildcard wildcard = (ResolvedWildcard)type;
            if (wildcard.isBounded()) {
                return isProperType(wildcard.getBoundedType());
            }
            return true;
        }
        if (type.isPrimitive()) {
            return true;
        }
        if (type.isTypeVariable()) {
            // FIXME I am not sure...
            return false;
        }
        if (type.isArray()) {
            return isProperType(type.asArrayType().getComponentType());
        }
        throw new UnsupportedOperationException(type.toString());
    }

    /**
     * see https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.3
     * @param expression
     * @param t
     * @return
     */
    public static boolean isCompatibleInAStrictInvocationContext(Expression expression, ResolvedType t) {
        throw new UnsupportedOperationException();
    }

    /**
     * see https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.3
     * @param expression
     * @param t
     * @return
     */
    public static boolean isCompatibleInALooseInvocationContext(TypeSolver typeSolver, Expression expression, ResolvedType t) {
        //throw new UnsupportedOperationException("Unable to determine if " + expression + " is compatible in a loose invocation context with type " + t);
        return isCompatibleInALooseInvocationContext(JavaParserFacade.get(typeSolver).getType(expression), t);
    }

    /**
     * see https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.3
     * @param s
     * @param t
     * @return
     */
    public static boolean isCompatibleInALooseInvocationContext(ResolvedType s, ResolvedType t) {
        // Loose invocation contexts allow a more permissive set of conversions, because they are only used for a
        // particular invocation if no applicable declaration can be found using strict invocation contexts. Loose
        // invocation contexts allow the use of one of the following:
        //
        // - an identity conversion (§5.1.1)

        if (s.equals(t)) {
            return true;
        }

        // - a widening primitive conversion (§5.1.2)

        if (s.isPrimitive() && t.isPrimitive() && areCompatibleThroughWideningPrimitiveConversion(s, t)) {
            return true;
        }

        // - a widening reference conversion (§5.1.5)

        if (s.isReferenceType() && t.isReferenceType() && areCompatibleThroughWideningReferenceConversion(s, t)) {
            return true;
        }

        // - a boxing conversion (§5.1.7) optionally followed by widening reference conversion

        if (s.isPrimitive() && t.isReferenceType() &&
                areCompatibleThroughWideningReferenceConversion(toBoxedType(s.asPrimitive()), t)) {
            return true;
        }

        // - an unboxing conversion (§5.1.8) optionally followed by a widening primitive conversion

        if (s.isReferenceType() && s.asReferenceType().isUnboxable() && t.isPrimitive() &&
                areCompatibleThroughWideningPrimitiveConversion(s.asReferenceType().toUnboxedType().get(), t)) {
            return true;
        }

        // If, after the conversions listed for an invocation context have been applied, the resulting type is a raw
        // type (§4.8), an unchecked conversion (§5.1.9) may then be applied.
        //
        // A value of the null type (the null reference is the only such value) may be assigned to any reference type
        if (s.isNull() && t.isReferenceType()) {
            return true;
        }

        //throw new UnsupportedOperationException("isCompatibleInALooseInvocationContext unable to decide on s=" + s + ", t=" + t);
        // TODO FIXME
        return t.isAssignableBy(s);
    }

    public static ResolvedType toBoxedType(ResolvedPrimitiveType primitiveType) {
        throw new UnsupportedOperationException();
    }

    // get the resolved boxed type of the specified primitive type
    public static ResolvedType toBoxedType(ResolvedPrimitiveType primitiveType, TypeSolver typeSolver ) {
        SymbolReference<ResolvedReferenceTypeDeclaration> typeDeclaration =  typeSolver.tryToSolveType(primitiveType.getBoxTypeQName());
        return new ReferenceTypeImpl(typeDeclaration.getCorrespondingDeclaration());
    }

    public static boolean areCompatibleThroughWideningReferenceConversion(ResolvedType s, ResolvedType t) {
        Optional<ResolvedPrimitiveType> correspondingPrimitiveTypeForS = Arrays.stream(ResolvedPrimitiveType.values()).filter(pt -> pt.getBoxTypeQName().equals(s.asReferenceType().getQualifiedName())).findFirst();
        if (!correspondingPrimitiveTypeForS.isPresent()) {
            return false;
        }
        throw new UnsupportedOperationException("areCompatibleThroughWideningReferenceConversion s="+s+", t=" + t);
    }

    public static boolean areCompatibleThroughWideningPrimitiveConversion(ResolvedType s, ResolvedType t) {
        if (s.isPrimitive() && t.isPrimitive()) {
            return s.isAssignableBy(t);
        }
        return false;
    }

    public static Set<InferenceVariable> usedInferenceVariables(ResolvedType type) {
        if (type.isInferenceVariable()) {
            return new HashSet<>(Arrays.asList((InferenceVariable) type));
        }
        if (type.isReferenceType()) {
            Set<InferenceVariable> res = new HashSet<>();
            for (ResolvedType tp : type.asReferenceType().typeParametersValues()) {
                res.addAll(usedInferenceVariables(tp));
            }
            return res;
        }
        throw new UnsupportedOperationException(type.toString());
    }

    /**
     * See JLS 4.10.4. Least Upper Bound.
     * The least upper bound, or "lub", of a set of reference types is a shared supertype that is more specific than
     * any other shared supertype (that is, no other shared supertype is a subtype of the least upper bound).
     */
    public static ResolvedType leastUpperBound(Set<ResolvedType> types) {
    	LeastUpperBoundLogic logic = LeastUpperBoundLogic.of();
    	return logic.lub(types);
    }

    /**
     * See JLS 15.27.3. Type of a Lambda Expression
     * @return
     */
    public static Pair<ResolvedType, Boolean> groundTargetTypeOfLambda(LambdaExpr lambdaExpr, ResolvedType T, TypeSolver typeSolver) {
        // The ground target type is derived from T as follows:
        //
        boolean used18_5_3 = false;

        boolean wildcardParameterized = T.asReferenceType().typeParametersValues().stream()
                .anyMatch(tp -> tp.isWildcard());
        if (wildcardParameterized) {
            // - If T is a wildcard-parameterized functional interface type and the lambda expression is explicitly typed,
            //   then the ground target type is inferred as described in §18.5.3.

            if (ExpressionHelper.isExplicitlyTyped(lambdaExpr)) {
                used18_5_3 = true;
                throw new UnsupportedOperationException();
            }
            return new Pair<>(nonWildcardParameterizationOf(T.asReferenceType(), typeSolver), used18_5_3);
        }

        // - Otherwise, the ground target type is T.
        return new Pair<>(T, used18_5_3);
    }

    /**
     * See JLS 9.9
     */
    private static ResolvedReferenceType nonWildcardParameterizationOf(ResolvedReferenceType originalType, TypeSolver typeSolver) {
        ResolvedReferenceTypeDeclaration originalTypeDeclaration = originalType.getTypeDeclaration().orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."));

        List<ResolvedType> TIs = new LinkedList<>();
        List<ResolvedType> AIs = originalType.typeParametersValues();
        List<ResolvedTypeParameterDeclaration> TPs = originalTypeDeclaration.getTypeParameters();

        // Let P1...Pn be the type parameters of I with corresponding bounds B1...Bn. For all i (1 ≤ i ≤ n),
        // Ti is derived according to the form of Ai:

        ResolvedReferenceType object = new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject());

        for (int i=0;i<AIs.size();i++) {
            ResolvedType Ai = AIs.get(i);
            ResolvedType Ti = null;

            // - If Ai is a type, then Ti = Ai.

            if (!Ai.isWildcard()) {
                Ti = Ai;
            }

            // - If Ai is a wildcard, and the corresponding type parameter's bound, Bi, mentions one of P1...Pn, then
            //   Ti is undefined and there is no function type.

            if (Ti == null && Ai.isWildcard() && Ai.asWildcard().mention(originalTypeDeclaration.getTypeParameters())) {
                throw new IllegalArgumentException();
            }

            // - Otherwise:

            if (Ti == null) {

                ResolvedType Bi = TPs.get(i).hasLowerBound() ? TPs.get(i).getLowerBound() : object;

                //   - If Ai is an unbound wildcard ?, then Ti = Bi.

                if (Ai.isWildcard() && !Ai.asWildcard().isBounded()) {
                    Ti = Bi;
                }

                //   - If Ai is a upper-bounded wildcard ? extends Ui, then Ti = glb(Ui, Bi) (§5.1.10).

                else if (Ai.isWildcard() && Ai.asWildcard().isUpperBounded()) {
                    ResolvedType Ui = Ai.asWildcard().getBoundedType();
                    Ti = glb(new HashSet<>(Arrays.asList(Ui, Bi)));
                }

                //   - If Ai is a lower-bounded wildcard ? super Li, then Ti = Li.

                else if (Ai.isWildcard() && Ai.asWildcard().isLowerBounded()) {
                    Ti = Ai.asWildcard().getBoundedType();
                }

                else {
                    throw new RuntimeException("This should not happen");
                }
            }

            TIs.add(Ti);
        }

        return new ReferenceTypeImpl(originalTypeDeclaration, TIs);
    }

    public static MethodType getFunctionType(ResolvedType type) {
        Optional<MethodUsage> mu = FunctionalInterfaceLogic.getFunctionalMethod(type);
        if (mu.isPresent()) {
            return MethodType.fromMethodUsage(mu.get());
        }
        throw new IllegalArgumentException();
    }

    /**
     * See JLS 5.1.10. Capture Conversion.
     */
    public static ResolvedType glb(Set<ResolvedType> types) {
        if (types.isEmpty()) {
            throw new IllegalArgumentException();
        }
        if (types.size() == 1) {
            return types.iterator().next();
        }
        return new ResolvedIntersectionType(types);
    }
}
