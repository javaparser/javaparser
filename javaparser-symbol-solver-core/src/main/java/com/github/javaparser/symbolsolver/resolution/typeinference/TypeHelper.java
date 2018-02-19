package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.logic.FunctionalInterfaceLogic;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.*;
import com.github.javaparser.utils.Pair;

import java.util.*;

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
        if (type instanceof ResolvedWildcard) {
            ResolvedWildcard wildcard = (ResolvedWildcard)type;
            if (wildcard.isBounded()) {
                return isProperType(wildcard.getBoundedType());
            } else {
                return true;
            }
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

        if (isUnboxable(s) && s.isReferenceType() && t.isPrimitive() &&
                areCompatibleThroughWideningPrimitiveConversion(toUnboxedType(s.asReferenceType()), t)) {
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

    private static boolean isUnboxable(ResolvedType referenceType) {
        if (!referenceType.isReferenceType()) {
            return false;
        }
        return Arrays.stream(ResolvedPrimitiveType.values()).anyMatch(pt -> referenceType.asReferenceType().getQualifiedName().equals(pt.getBoxTypeQName()));
    }

    private static ResolvedType toUnboxedType(ResolvedReferenceType referenceType) {
        throw new UnsupportedOperationException(referenceType.toString());
    }

    private static ResolvedType toBoxedType(ResolvedPrimitiveType primitiveType) {
        throw new UnsupportedOperationException();
    }

    private static boolean areCompatibleThroughWideningReferenceConversion(ResolvedType s, ResolvedType t) {
        Optional<ResolvedPrimitiveType> correspondingPrimitiveTypeForS = Arrays.stream(ResolvedPrimitiveType.values()).filter(pt -> pt.getBoxTypeQName().equals(s.asReferenceType().getQualifiedName())).findFirst();
        if (!correspondingPrimitiveTypeForS.isPresent()) {
            return false;
        }
        throw new UnsupportedOperationException("areCompatibleThroughWideningReferenceConversion s="+s+", t=" + t);
    }

    private static boolean areCompatibleThroughWideningPrimitiveConversion(ResolvedType s, ResolvedType t) {
        if (s.isPrimitive() && t.isPrimitive()) {
            return s.isAssignableBy(t);
        } else {
            return false;
        }
    }

    public static boolean isInferenceVariable(ResolvedType type) {
        return type instanceof InferenceVariable;
    }

    public static Set<InferenceVariable> usedInferenceVariables(ResolvedType type) {
        if (isInferenceVariable(type)) {
            return new HashSet<>(Arrays.asList((InferenceVariable)type));
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
     */
    public static ResolvedType leastUpperBound(Set<ResolvedType> types) {
        if (types.size() == 0) {
            throw new IllegalArgumentException();
        }

        // The least upper bound, or "lub", of a set of reference types is a shared supertype that is more specific than
        // any other shared supertype (that is, no other shared supertype is a subtype of the least upper bound).
        // This type, lub(U1, ..., Uk), is determined as follows.
        //
        // If k = 1, then the lub is the type itself: lub(U) = U.

        if (types.size() == 1) {
            return types.stream().findFirst().get();
        }

        //
        //Otherwise:
        //
        //For each Ui (1 ≤ i ≤ k):
        //
        //Let ST(Ui) be the set of supertypes of Ui.
        //
        //Let EST(Ui), the set of erased supertypes of Ui, be:
        //
        //EST(Ui) = { |W| | W in ST(Ui) } where |W| is the erasure of W.
        //
        //The reason for computing the set of erased supertypes is to deal with situations where the set of types includes several distinct parameterizations of a generic type.
        //
        //For example, given List<String> and List<Object>, simply intersecting the sets ST(List<String>) = { List<String>, Collection<String>, Object } and ST(List<Object>) = { List<Object>, Collection<Object>, Object } would yield a set { Object }, and we would have lost track of the fact that the upper bound can safely be assumed to be a List.
        //
        //In contrast, intersecting EST(List<String>) = { List, Collection, Object } and EST(List<Object>) = { List, Collection, Object } yields { List, Collection, Object }, which will eventually enable us to produce List<?>.
        //
        //Let EC, the erased candidate set for U1 ... Uk, be the intersection of all the sets EST(Ui) (1 ≤ i ≤ k).
        //
        //Let MEC, the minimal erased candidate set for U1 ... Uk, be:
        //
        //MEC = { V | V in EC, and for all W ≠ V in EC, it is not the case that W <: V }
        //
        //Because we are seeking to infer more precise types, we wish to filter out any candidates that are supertypes of other candidates. This is what computing MEC accomplishes. In our running example, we had EC = { List, Collection, Object }, so MEC = { List }. The next step is to recover type arguments for the erased types in MEC.
        //
        //For any element G of MEC that is a generic type:
        //
        //Let the "relevant" parameterizations of G, Relevant(G), be:
        //
        //Relevant(G) = { V | 1 ≤ i ≤ k: V in ST(Ui) and V = G<...> }
        //
        //In our running example, the only generic element of MEC is List, and Relevant(List) = { List<String>, List<Object> }. We will now seek to find a type argument for List that contains (§4.5.1) both String and Object.
        //
        //This is done by means of the least containing parameterization (lcp) operation defined below. The first line defines lcp() on a set, such as Relevant(List), as an operation on a list of the elements of the set. The next line defines the operation on such lists, as a pairwise reduction on the elements of the list. The third line is the definition of lcp() on pairs of parameterized types, which in turn relies on the notion of least containing type argument (lcta). lcta() is defined for all possible cases.
        //
        //Let the "candidate" parameterization of G, Candidate(G), be the most specific parameterization of the generic type G that contains all the relevant parameterizations of G:
        //
        //Candidate(G) = lcp(Relevant(G))
        //
        //where lcp(), the least containing invocation, is:
        //
        //lcp(S) = lcp(e1, ..., en) where ei (1 ≤ i ≤ n) in S
        //
        //lcp(e1, ..., en) = lcp(lcp(e1, e2), e3, ..., en)
        //
        //lcp(G<X1, ..., Xn>, G<Y1, ..., Yn>) = G<lcta(X1, Y1), ..., lcta(Xn, Yn)>
        //
        //lcp(G<X1, ..., Xn>) = G<lcta(X1), ..., lcta(Xn)>
        //
        //and where lcta(), the least containing type argument, is: (assuming U and V are types)
        //
        //lcta(U, V) = U if U = V, otherwise ? extends lub(U, V)
        //
        //lcta(U, ? extends V) = ? extends lub(U, V)
        //
        //lcta(U, ? super V) = ? super glb(U, V)
        //
        //lcta(? extends U, ? extends V) = ? extends lub(U, V)
        //
        //lcta(? extends U, ? super V) = U if U = V, otherwise ?
        //
        //lcta(? super U, ? super V) = ? super glb(U, V)
        //
        //lcta(U) = ? if U's upper bound is Object, otherwise ? extends lub(U,Object)
        //
        //and where glb() is as defined in §5.1.10.
        //
        //Let lub(U1 ... Uk) be:
        //
        //Best(W1) & ... & Best(Wr)
        //
        //where Wi (1 ≤ i ≤ r) are the elements of MEC, the minimal erased candidate set of U1 ... Uk;
        //
        //and where, if any of these elements are generic, we use the candidate parameterization (so as to recover type arguments):
        //
        //Best(X) = Candidate(X) if X is generic; X otherwise.
        //
        //Strictly speaking, this lub() function only approximates a least upper bound. Formally, there may exist some other type T such that all of U1 ... Uk are subtypes of T and T is a subtype of lub(U1, ..., Uk). However, a compiler for the Java programming language must implement lub() as specified above.
        //
        //It is possible that the lub() function yields an infinite type. This is permissible, and a compiler for the Java programming language must recognize such situations and represent them appropriately using cyclic data structures.
        //
        //The possibility of an infinite type stems from the recursive calls to lub(). Readers familiar with recursive types should note that an infinite type is not the same as a recursive type
        throw new UnsupportedOperationException();
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

            // - If T is a wildcard-parameterized functional interface type and the lambda expression is implicitly typed,
            //   then the ground target type is the non-wildcard parameterization (§9.9) of T.

            else {
                return new Pair<>(nonWildcardParameterizationOf(T.asReferenceType(), typeSolver), used18_5_3);
            }
        }

        // - Otherwise, the ground target type is T.
        return new Pair<>(T, used18_5_3);
    }

    /**
     * See JLS 9.9
     */
    private static ResolvedReferenceType nonWildcardParameterizationOf(ResolvedReferenceType originalType, TypeSolver typeSolver) {
        List<ResolvedType> TIs = new LinkedList<>();
        List<ResolvedType> AIs = originalType.typeParametersValues();
        List<ResolvedTypeParameterDeclaration> TPs = originalType.getTypeDeclaration().getTypeParameters();

        // Let P1...Pn be the type parameters of I with corresponding bounds B1...Bn. For all i (1 ≤ i ≤ n),
        // Ti is derived according to the form of Ai:

        ResolvedReferenceType object = new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);

        for (int i=0;i<AIs.size();i++) {
            ResolvedType Ai = AIs.get(i);
            ResolvedType Ti = null;

            // - If Ai is a type, then Ti = Ai.

            if (!Ai.isWildcard()) {
                Ti = Ai;
            }

            // - If Ai is a wildcard, and the corresponding type parameter's bound, Bi, mentions one of P1...Pn, then
            //   Ti is undefined and there is no function type.

            if (Ti == null && Ai.isWildcard() && Ai.asWildcard().mention(originalType.getTypeDeclaration().getTypeParameters())) {
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

                else throw new RuntimeException("This should not happen");
            }

            TIs.add(Ti);
        }

        return new ReferenceTypeImpl(originalType.getTypeDeclaration(), TIs, typeSolver);
    }

    public static MethodType getFunctionType(ResolvedType type) {
        Optional<MethodUsage> mu = FunctionalInterfaceLogic.getFunctionalMethod(type);
        if (mu.isPresent()) {
            return MethodType.fromMethodUsage(mu.get());
        } else {
            throw new IllegalArgumentException();
        }
    }

    /**
     * See JLS 5.1.10. Capture Conversion.
     */
    public static ResolvedType glb(Set<ResolvedType> types) {
        if (types.size() == 0) {
            throw new IllegalArgumentException();
        }
        if (types.size() == 1) {
            return types.iterator().next();
        }
        return new ResolvedIntersectionType(types);
    }
}
