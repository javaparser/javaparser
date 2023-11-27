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

import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.SubtypeOfBound;
import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.ThrowsBound;
import com.github.javaparser.symbolsolver.resolution.typeinference.constraintformulas.ExpressionCompatibleWithType;

/**
 * The API exposed by the TypeInference subsystem.
 *
 * @author Federico Tomassetti
 */
public class TypeInference {

    private final ResolvedType object;
    private TypeSolver typeSolver;

    public TypeInference(TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new NullPointerException();
        }
        this.typeSolver = typeSolver;
        this.object = new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject());
    }

    ///
    /// Public static methods
    ///

    public static MethodUsage toMethodUsage(MethodCallExpr call, ResolvedMethodDeclaration methodDeclaration, TypeSolver typeSolver) {
        TypeInference typeInference = new TypeInference(typeSolver);
        Optional<InstantiationSet> instantiationSetOpt = typeInference.instantiationInference(call, methodDeclaration);
        if (instantiationSetOpt.isPresent()) {
            return instantiationSetToMethodUsage(methodDeclaration, instantiationSetOpt.get());
        }
        throw new IllegalArgumentException();
    }

    ///
    /// Public instance methods
    ///

    public Optional<InstantiationSet> instantiationInference(MethodCallExpr methodCallExpr, ResolvedMethodDeclaration methodDeclaration) {
        return instantiationInference(methodCallExpr.getArguments(), methodDeclaration);
    }

    public Optional<InstantiationSet> instantiationInference(List<Expression> argumentExpressions, ResolvedMethodDeclaration methodDeclaration) {
//        if (methodCallExpr.getTypeArguments().isPresent()) {
//            throw new IllegalArgumentException("Type inference unnecessary as type arguments have been specified");
//        }

        // Given a method invocation that provides no explicit type arguments, the process to determine whether a
        // potentially applicable generic method m is applicable is as follows:

        // - Where P1, ..., Pp (p ≥ 1) are the type parameters of m, let α1, ..., αp be inference variables, and
        //   let θ be the substitution [P1:=α1, ..., Pp:=αp].

        List<ResolvedTypeParameterDeclaration> Ps = methodDeclaration.getTypeParameters();
        List<InferenceVariable> alphas = InferenceVariable.instantiate(Ps);
        Substitution theta = Substitution.empty();
        for (int i=0;i<Ps.size();i++) {
            theta = theta.withPair(Ps.get(0), alphas.get(0));
        }

        // - An initial bound set, B0, is constructed from the declared bounds of P1, ..., Pp, as described in §18.1.3.

        BoundSet B0 = boundSetup(Ps, alphas);

        // - For all i (1 ≤ i ≤ p), if Pi appears in the throws clause of m, then the bound throws αi is implied.
        //   These bounds, if any, are incorporated with B0 to produce a new bound set, B1.

        BoundSet B1 = B0;
        for (int i=0;i<Ps.size();i++) {
            ResolvedTypeParameterDeclaration Pi = Ps.get(i);
            if (appearInThrowsClause(Pi, methodDeclaration)) {
                B1 = B1.withBound(new ThrowsBound(alphas.get(i)));
            }
        }

        // - A set of constraint formulas, C, is constructed as follows.
        //
        //   Let F1, ..., Fn be the formal parameter types of m, and let e1, ..., ek be the actual argument expressions
        //   of the invocation. Then:

        List<ResolvedType> Fs = formalParameterTypes(methodDeclaration);
        List<Expression> es = argumentExpressions;

        Optional<ConstraintFormulaSet> C = Optional.empty();

        //   - To test for applicability by strict invocation:

        if (!C.isPresent()) {
            C = testForApplicabilityByStrictInvocation(Fs, es, theta);
        }

        //   - To test for applicability by loose invocation:

        if (!C.isPresent()) {
            C = testForApplicabilityByLooseInvocation(Fs, es, theta);
        }

        //   - To test for applicability by variable arity invocation:

        if (!C.isPresent()) {
            C = testForApplicabilityByVariableArityInvocation(Fs, es, theta);
        }

        if (!C.isPresent()) {
            return Optional.empty();
        }

        // - C is reduced (§18.2) and the resulting bounds are incorporated with B1 to produce a new bound set, B2.

        BoundSet resultingBounds = C.get().reduce(typeSolver);
        BoundSet B2 = B1.incorporate(resultingBounds, typeSolver);

        // - Finally, the method m is applicable if B2 does not contain the bound false and resolution of all the
        //   inference variables in B2 succeeds (§18.4).

        if (B2.containsFalse()) {
            return Optional.empty();
        }

        Optional<InstantiationSet> instantiation = B2.performResolution(alphas, typeSolver);
        return instantiation;
    }

    /**
     * Determine whether a potentially applicable generic method m is applicable for a method invocation that
     * provides no explicit type arguments.
     */
    public boolean invocationApplicabilityInference(MethodCallExpr methodCallExpr, ResolvedMethodDeclaration methodDeclaration) {
        if (!methodCallExpr.getNameAsString().equals(methodDeclaration.getName())) {
            throw new IllegalArgumentException();
        }
        Optional<InstantiationSet> partial = instantiationInference(methodCallExpr, methodDeclaration);
        if (!partial.isPresent()) {
            return false;
        }
        int nActualParams = methodCallExpr.getArguments().size();
        int nFormalParams = methodDeclaration.getNumberOfParams();
        if (nActualParams != nFormalParams) {
            if (methodDeclaration.hasVariadicParameter()) {
                if (nActualParams < (nFormalParams - 1)) {
                    return false;
                }
            } else {
                return false;
            }
        }
        //MethodUsage methodUsage = instantiationSetToMethodUsage(methodDeclaration, partial.get());
//        for (int i=0;i<nActualParams;i++) {
//            int formalIndex = i >= nFormalParams ? nFormalParams - 1 : i;
//            Type formalType = methodDeclaration.getParam(formalIndex).getType();
//            Type actualType = JavaParserFacade.get(typeSolver).getType(methodCallExpr.getArgument(i));
//            //if (!formalType.isAssignableBy(actualType)) {
//            //    return false;
//            //}
//        }
        return true;
    }

    public BoundSet invocationTypeInferenceBoundsSetB3() {
        // Given a method invocation that provides no explicit type arguments, and a corresponding most specific
        // applicable generic method m, the process to infer the invocation type (§15.12.2.6) of the chosen method is
        // as follows:
        //
        // - Let θ be the substitution [P1:=α1, ..., Pp:=αp] defined in §18.5.1 to replace the type parameters of m with inference variables.
        //
        // - Let B2 be the bound set produced by reduction in order to demonstrate that m is applicable in §18.5.1. (While it was necessary in §18.5.1 to demonstrate that the inference variables in B2 could be resolved, in order to establish applicability, the instantiations produced by this resolution step are not considered part of B2.)
        //
        // - If the invocation is not a poly expression, let the bound set B3 be the same as B2.
        //
        //   If the invocation is a poly expression, let the bound set B3 be derived from B2 as follows. Let R be the
        //   return type of m, let T be the invocation's target type, and then:
        //
        //   - If unchecked conversion was necessary for the method to be applicable during constraint set reduction
        //     in §18.5.1, the constraint formula ‹|R| → T› is reduced and incorporated with B2.
        //
        //   - Otherwise, if R θ is a parameterized type, G<A1, ..., An>, and one of A1, ..., An is a wildcard, then,
        //     for fresh inference variables β1, ..., βn, the constraint formula ‹G<β1, ..., βn> → T› is reduced and
        //     incorporated, along with the bound G<β1, ..., βn> = capture(G<A1, ..., An>), with B2.
        //
        //   - Otherwise, if R θ is an inference variable α, and one of the following is true:
        //
        //     - T is a reference type, but is not a wildcard-parameterized type, and either i) B2 contains a bound of
        //       one of the forms α = S or S <: α, where S is a wildcard-parameterized type, or ii) B2 contains two
        //       bounds of the forms S1 <: α and S2 <: α, where S1 and S2 have supertypes that are two different
        //       parameterizations of the same generic class or interface.
        //
        //     - T is a parameterization of a generic class or interface, G, and B2 contains a bound of one of the
        //       forms α = S or S <: α, where there exists no type of the form G<...> that is a supertype of S, but the
        //       raw type |G<...>| is a supertype of S.
        //
        //     - T is a primitive type, and one of the primitive wrapper classes mentioned in §5.1.7 is an
        //       instantiation, upper bound, or lower bound for α in B2.
        //
        //     then α is resolved in B2, and where the capture of the resulting instantiation of α is U, the constraint
        //     formula ‹U → T› is reduced and incorporated with B2.
        //
        //   - Otherwise, the constraint formula ‹R θ → T› is reduced and incorporated with B2.
        throw new UnsupportedOperationException();
    }

    public void invocationTypeInference() {
        BoundSet B3 = invocationTypeInferenceBoundsSetB3();
        //
        //A set of constraint formulas, C, is constructed as follows.
        //
        //        Let e1, ..., ek be the actual argument expressions of the invocation. If m is applicable by strict or loose invocation, let F1, ..., Fk be the formal parameter types of m; if m is applicable by variable arity invocation, let F1, ..., Fk the first k variable arity parameter types of m (§15.12.2.4). Then:
        //
        //For all i (1 ≤ i ≤ k), if ei is not pertinent to applicability, C contains ‹ei → Fi θ›.
        //
        //For all i (1 ≤ i ≤ k), additional constraints may be included, depending on the form of ei:
        //
        //If ei is a LambdaExpression, C contains ‹LambdaExpression →throws Fi θ›.
        //
        //In addition, the lambda body is searched for additional constraints:
        //
        //For a block lambda body, the search is applied recursively to each result expression.
        //
        //For a poly class instance creation expression (§15.9) or a poly method invocation expression (§15.12), C contains all the constraint formulas that would appear in the set C generated by §18.5.2 when inferring the poly expression's invocation type.
        //
        //For a parenthesized expression, the search is applied recursively to the contained expression.
        //
        //For a conditional expression, the search is applied recursively to the second and third operands.
        //
        //For a lambda expression, the search is applied recursively to the lambda body.
        //
        //If ei is a MethodReference, C contains ‹MethodReference →throws Fi θ›.
        //
        //If ei is a poly class instance creation expression (§15.9) or a poly method invocation expression (§15.12), C contains all the constraint formulas that would appear in the set C generated by §18.5.2 when inferring the poly expression's invocation type.
        //
        //If ei is a parenthesized expression, these rules are applied recursively to the contained expression.
        //
        //If ei is a conditional expression, these rules are applied recursively to the second and third operands.
        //
        //While C is not empty, the following process is repeated, starting with the bound set B3 and accumulating new bounds into a "current" bound set, ultimately producing a new bound set, B4:
        //
        //A subset of constraints is selected in C, satisfying the property that, for each constraint, no input variable can influence an output variable of another constraint in C. The terms input variable and output variable are defined below. An inference variable α can influence an inference variable β if α depends on the resolution of β (§18.4), or vice versa; or if there exists a third inference variable γ such that α can influence γ and γ can influence β.
        //
        //If this subset is empty, then there is a cycle (or cycles) in the graph of dependencies between constraints. In this case, all constraints are considered that participate in a dependency cycle (or cycles) and do not depend on any constraints outside of the cycle (or cycles). A single constraint is selected from the considered constraints, as follows:
        //
        //If any of the considered constraints have the form ‹Expression → T›, then the selected constraint is the considered constraint of this form that contains the expression to the left (§3.5) of the expression of every other considered constraint of this form.
        //
        //        If no considered constraint has the form ‹Expression → T›, then the selected constraint is the considered constraint that contains the expression to the left of the expression of every other considered constraint.
        //
        //        The selected constraint(s) are removed from C.
        //
        //        The input variables α1, ..., αm of all the selected constraint(s) are resolved.
        //
        //        Where T1, ..., Tm are the instantiations of α1, ..., αm, the substitution [α1:=T1, ..., αm:=Tm] is applied to every constraint.
        //
        //        The constraint(s) resulting from substitution are reduced and incorporated with the current bound set.
        //
        //Finally, if B4 does not contain the bound false, the inference variables in B4 are resolved.
        //
        //If resolution succeeds with instantiations T1, ..., Tp for inference variables α1, ..., αp, let θ' be the substitution [P1:=T1, ..., Pp:=Tp]. Then:
        //
        //If unchecked conversion was necessary for the method to be applicable during constraint set reduction in §18.5.1, then the parameter types of the invocation type of m are obtained by applying θ' to the parameter types of m's type, and the return type and thrown types of the invocation type of m are given by the erasure of the return type and thrown types of m's type.
        //
        //If unchecked conversion was not necessary for the method to be applicable, then the invocation type of m is obtained by applying θ' to the type of m.
        //
        //If B4 contains the bound false, or if resolution fails, then a compile-time error occurs.
        //
        //Invocation type inference may require carefully sequencing the reduction of constraint formulas of the forms ‹Expression → T›, ‹LambdaExpression →throws T›, and ‹MethodReference →throws T›. To facilitate this sequencing, the input variables of these constraints are defined as follows:
        //
        //For ‹LambdaExpression → T›:
        //
        //If T is an inference variable, it is the (only) input variable.
        //
        //        If T is a functional interface type, and a function type can be derived from T (§15.27.3), then the input variables include i) if the lambda expression is implicitly typed, the inference variables mentioned by the function type's parameter types; and ii) if the function type's return type, R, is not void, then for each result expression e in the lambda body (or for the body itself if it is an expression), the input variables of ‹e → R›.
        //
        //Otherwise, there are no input variables.
        //
        //For ‹LambdaExpression →throws T›:
        //
        //If T is an inference variable, it is the (only) input variable.
        //
        //        If T is a functional interface type, and a function type can be derived, as described in §15.27.3, the input variables include i) if the lambda expression is implicitly typed, the inference variables mentioned by the function type's parameter types; and ii) the inference variables mentioned by the function type's return type.
        //
        //        Otherwise, there are no input variables.
        //
        //        For ‹MethodReference → T›:
        //
        //If T is an inference variable, it is the (only) input variable.
        //
        //        If T is a functional interface type with a function type, and if the method reference is inexact (§15.13.1), the input variables are the inference variables mentioned by the function type's parameter types.
        //
        //Otherwise, there are no input variables.
        //
        //For ‹MethodReference →throws T›:
        //
        //If T is an inference variable, it is the (only) input variable.
        //
        //        If T is a functional interface type with a function type, and if the method reference is inexact (§15.13.1), the input variables are the inference variables mentioned by the function type's parameter types and the function type's return type.
        //
        //        Otherwise, there are no input variables.
        //
        //        For ‹Expression → T›, if Expression is a parenthesized expression:
        //
        //Where the contained expression of Expression is Expression', the input variables are the input variables of ‹Expression' → T›.
        //
        //For ‹ConditionalExpression → T›:
        //
        //Where the conditional expression has the form e1 ? e2 : e3, the input variables are the input variables of ‹e2 → T› and ‹e3 → T›.
        //
        //For all other constraint formulas, there are no input variables.
        //
        //The output variables of these constraints are all inference variables mentioned by the type on the right-hand side of the constraint, T, that are not input variables.

        throw new UnsupportedOperationException();
    }

    public void functionalInterfaceParameterizationInference(LambdaExpr lambdaExpr,
                                                             ResolvedInterfaceDeclaration interfaceDeclaration) {
        // Where a lambda expression with explicit parameter types P1, ..., Pn targets a functional interface
        // type F<A1, ..., Am> with at least one wildcard type argument, then a parameterization of F may be derived
        // as the ground target type of the lambda expression as follows.

        int n = lambdaExpr.getParameters().size();

        if (interfaceDeclaration.getTypeParameters().isEmpty()) {
            throw new IllegalArgumentException("Functional Interface without type arguments");
        }

        // Let Q1, ..., Qk be the parameter types of the function type of the type F<α1, ..., αm>,
        // where α1, ..., αm are fresh inference variables.

        int k = interfaceDeclaration.getTypeParameters().size();
        List<InferenceVariable> alphas = InferenceVariable.instantiate(interfaceDeclaration.getTypeParameters());

        TypeInferenceCache.recordInferenceVariables(typeSolver, lambdaExpr, alphas);

        // If n ≠ k, no valid parameterization exists.

        if (n != k) {
            throw new IllegalArgumentException("No valida parameterization can exist has n=" + " and k=" + k);
        }

        // Otherwise, a set of constraint formulas is formed with, for
        // all i (1 ≤ i ≤ n), ‹Pi = Qi›. This constraint formula set is reduced to form the bound set B.

        ConstraintFormulaSet constraintFormulaSet = ConstraintFormulaSet.empty();
        for (int i=0; i<n; i++) {
            throw new UnsupportedOperationException();
            //Type pi = JavaParserFacade.get(typeSolver).convertToUsage(lambdaExpr.getParameters().get(i).getType(), lambdaExpr);
            //Type qi = JavaParserFacade.get(typeSolver).convertToUsage(interfaceDeclaration.getm.get(i).getType(), lambdaExpr);
            //constraintFormulaSet = constraintFormulaSet.withConstraint(new TypeSameAsType(pi, qi));
        }
        BoundSet B = constraintFormulaSet.reduce(typeSolver);

        // If B contains the bound false, no valid parameterization exists. Otherwise, a new parameterization of the
        // functional interface type, F<A'1, ..., A'm>, is constructed as follows, for 1 ≤ i ≤ m:
        //
        // - If B contains an instantiation (§18.1.3) for αi, T, then A'i = T.
        //
        // - Otherwise, A'i = Ai.
        //
        // If F<A'1, ..., A'm> is not a well-formed type (that is, the type arguments are not within their bounds), or if F<A'1, ..., A'm> is not a subtype of F<A1, ..., Am>, no valid parameterization exists. Otherwise, the inferred parameterization is either F<A'1, ..., A'm>, if all the type arguments are types, or the non-wildcard parameterization (§9.9) of F<A'1, ..., A'm>, if one or more type arguments are still wildcards.

        throw new UnsupportedOperationException();
    }

    /**
     * Return if m2 is more specific than m1
     * @param methodCall
     * @param m1
     * @param m2
     */
    public boolean moreSpecificMethodInference(MethodCallExpr methodCall, ResolvedMethodDeclaration m1, ResolvedMethodDeclaration m2) {
        // When testing that one applicable method is more specific than another (§15.12.2.5), where the second method
        // is generic, it is necessary to test whether some instantiation of the second method's type parameters can be
        // inferred to make the first method more specific than the second.

        if (!m2.isGeneric()) {
            throw new IllegalArgumentException("M2 is not generic (m2: " + m2 + ")");
        }

        // Let m1 be the first method and m2 be the second method. Where m2 has type parameters P1, ..., Pp,
        // let α1, ..., αp be inference variables, and let θ be the substitution [P1:=α1, ..., Pp:=αp].
        //
        // Let e1, ..., ek be the argument expressions of the corresponding invocation. Then:
        //
        // - If m1 and m2 are applicable by strict or loose invocation (§15.12.2.2, §15.12.2.3), then let S1, ..., Sk be the formal parameter types of m1, and let T1, ..., Tk be the result of θ applied to the formal parameter types of m2.
        //
        // - If m1 and m2 are applicable by variable arity invocation (§15.12.2.4), then let S1, ..., Sk be the first k variable arity parameter types of m1, and let T1, ..., Tk be the result of θ applied to the first k variable arity parameter types of m2.
        //
        // Note that no substitution is applied to S1, ..., Sk; even if m1 is generic, the type parameters of m1 are treated as type variables, not inference variables.
        //
        // The process to determine if m1 is more specific than m2 is as follows:
        //
        // - First, an initial bound set, B, is constructed from the declared bounds of P1, ..., Pp, as specified in §18.1.3.
        //
        // - Second, for all i (1 ≤ i ≤ k), a set of constraint formulas or bounds is generated.
        //
        //   If Ti is a proper type, the result is true if Si is more specific than Ti for ei (§15.12.2.5), and false otherwise. (Note that Si is always a proper type.)
        //
        //   Otherwise, if Ti is not a functional interface type, the constraint formula ‹Si <: Ti› is generated.
        //
        //   Otherwise, Ti is a parameterization of a functional interface, I. It must be determined whether Si satisfies the following five conditions:
        //
        //   1. Si is a functional interface type.
        //
        //   2. Si is not a superinterface of I, nor a parameterization of a superinterface of I.
        //
        //   3. Si is not a subinterface of I, nor a parameterization of a subinterface of I.
        //
        //   4. If Si is an intersection type, at least one element of the intersection is not a superinterface of I, nor a parameterization of a superinterface of I.
        //
        //   5. If Si is an intersection type, no element of the intersection is a subinterface of I, nor a parameterization of a subinterface of I.
        //
        //   If all five conditions are true, then the following constraint formulas or bounds are generated (where U1 ... Uk and R1 are the parameter types and return type of the function type of the capture of Si, and V1 ... Vk and R2 are the parameter types and return type of the function type of Ti):
        //
        //   - If ei is an explicitly typed lambda expression:
        //
        //     - For all j (1 ≤ j ≤ k), ‹Uj = Vj›.
        //
        //     - If R2 is void, true.
        //
        //     - Otherwise, if R1 and R2 are functional interface types, and neither interface is a subinterface of the other, and ei has at least one result expression, then these rules are applied recursively to R1 and R2, for each result expression in ei.
        //
        //     - Otherwise, if R1 is a primitive type and R2 is not, and ei has at least one result expression, and each result expression of ei is a standalone expression (§15.2) of a primitive type, true.
        //
        //     - Otherwise, if R2 is a primitive type and R1 is not, and ei has at least one result expression, and each result expression of ei is either a standalone expression of a reference type or a poly expression, true.
        //
        //     - Otherwise, ‹R1 <: R2›.
        //
        //   - If ei is an exact method reference:
        //
        //     - For all j (1 ≤ j ≤ k), ‹Uj = Vj›.
        //
        //     - If R2 is void, true.
        //
        //     - Otherwise, if R1 is a primitive type and R2 is not, and the compile-time declaration for ei has a primitive return type, true.
        //
        //     - Otherwise if R2 is a primitive type and R1 is not, and the compile-time declaration for ei has a reference return type, true.
        //
        //     - Otherwise, ‹R1 <: R2›.
        //
        //   - If ei is a parenthesized expression, these rules are applied recursively to the contained expression.
        //
        //   - If ei is a conditional expression, these rules are applied recursively to each of the second and third operands.
        //
        //   - Otherwise, false.
        //
        //   If the five constraints on Si are not satisfied, the constraint formula ‹Si <: Ti› is generated instead.
        //
        // - Third, if m2 is applicable by variable arity invocation and has k+1 parameters, then where Sk+1 is the k+1'th variable arity parameter type of m1 and Tk+1 is the result of θ applied to the k+1'th variable arity parameter type of m2, the constraint ‹Sk+1 <: Tk+1› is generated.
        //
        // - Fourth, the generated bounds and constraint formulas are reduced and incorporated with B to produce a bound set B'.
        //
        //   If B' does not contain the bound false, and resolution of all the inference variables in B' succeeds, then m1 is more specific than m2.
        //
        //   Otherwise, m1 is not more specific than m2.

        throw new UnsupportedOperationException();
    }


    ///
    /// Private static methods
    ///

    private static MethodUsage instantiationSetToMethodUsage(ResolvedMethodDeclaration methodDeclaration, InstantiationSet instantiationSet) {
        if (instantiationSet.isEmpty()) {
            return new MethodUsage(methodDeclaration);
        }
        List<ResolvedType> paramTypes = new LinkedList<>();
        for (int i=0;i<methodDeclaration.getNumberOfParams();i++) {
            paramTypes.add(instantiationSet.apply(methodDeclaration.getParam(i).getType()));
        }
        ResolvedType returnType = instantiationSet.apply(methodDeclaration.getReturnType());
        return new MethodUsage(methodDeclaration, paramTypes, returnType);
    }

    ///
    /// Private instance methods
    ///

    /**
     * When inference begins, a bound set is typically generated from a list of type parameter declarations P1, ..., Pp
     * and associated inference variables α1, ..., αp
     *
     * @param typeParameterDeclarations
     * @param inferenceVariables
     * @return
     */
    private BoundSet boundSetup(List<ResolvedTypeParameterDeclaration> typeParameterDeclarations, List<InferenceVariable> inferenceVariables) {
        if (typeParameterDeclarations.size() != inferenceVariables.size()) {
            throw new IllegalArgumentException();
        }

        // When inference begins, a bound set is typically generated from a list of
        // type parameter declarations P1, ..., Pp and associated inference variables α1, ..., αp.
        // Such a bound set is constructed as follows. For each l (1 ≤ l ≤ p):

        BoundSet boundSet = BoundSet.empty();

        for (int l=0;l<typeParameterDeclarations.size();l++) {
            ResolvedTypeParameterDeclaration Pl = typeParameterDeclarations.get(l);
            InferenceVariable alphaL = inferenceVariables.get(l);

            // - If Pl has no TypeBound, the bound αl <: Object appears in the set.

            if (Pl.getBounds().isEmpty()) {
                boundSet = boundSet.withBound(new SubtypeOfBound(alphaL, object));
            } else {

                // - Otherwise, for each type T delimited by & in the TypeBound, the bound αl <: T[P1:=α1, ..., Pp:=αp] appears
                // in the set; if this results in no proper upper bounds for αl (only dependencies), then the
                // bound αl <: Object also appears in the set.

                for (ResolvedTypeParameterDeclaration.Bound bound : Pl.getBounds()) {
                    ResolvedType T = bound.getType();
                    Substitution substitution = Substitution.empty();
                    for (int j=0;j<typeParameterDeclarations.size();j++) {
                        substitution = substitution.withPair(typeParameterDeclarations.get(j), inferenceVariables.get(j));
                    }
                    ResolvedType TWithSubstitutions = substitution.apply(T);

                    boundSet = boundSet.withBound(new SubtypeOfBound(alphaL, TWithSubstitutions));

                    if (boundSet.getProperUpperBoundsFor(alphaL).isEmpty()) {
                        boundSet = boundSet.withBound(new SubtypeOfBound(alphaL, object));
                    }
                }
            }
        }

        return boundSet;
    }

    private boolean appearInThrowsClause(ResolvedTypeParameterDeclaration p, ResolvedMethodDeclaration methodDeclaration) {
        for (ResolvedType thrownType : methodDeclaration.getSpecifiedExceptions()) {
            if (thrownType.isTypeVariable() && thrownType.asTypeVariable().asTypeParameter().equals(p)) {
                return true;
            }
        }
        return false;
    }

    private List<ResolvedType> formalParameterTypes(ResolvedMethodDeclaration methodDeclaration) {
        List<ResolvedType> types = new LinkedList<>();
        for (int i=0;i<methodDeclaration.getNumberOfParams();i++) {
            types.add(methodDeclaration.getParam(i).getType());
        }
        return types;
    }

    private boolean isImplicitlyTyped(LambdaExpr lambdaExpr) {
        return lambdaExpr.getParameters().stream().anyMatch(p -> p.getType() instanceof UnknownType);
    }

    private boolean isInexact(MethodReferenceExpr methodReferenceExpr) {
        throw new UnsupportedOperationException();
    }

    private boolean isPertinentToApplicability(Expression argument) {
        // An argument expression is considered pertinent to applicability for a potentially applicable method m
        // unless it has one of the following forms:
        //
        // - An implicitly typed lambda expression (§15.27.1).

        if (argument instanceof LambdaExpr) {
            LambdaExpr lambdaExpr = (LambdaExpr)argument;
            if (isImplicitlyTyped(lambdaExpr)) {
                return false;
            }
        }

        // - An inexact method reference expression (§15.13.1).

        if (argument instanceof MethodReferenceExpr) {
            MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr)argument;
            if (isInexact(methodReferenceExpr)) {
                return false;
            }
        }

        // - If m is a generic method and the method invocation does not provide explicit type arguments, an
        //   explicitly typed lambda expression or an exact method reference expression for which the
        //   corresponding target type (as derived from the signature of m) is a type parameter of m.

        if (argument instanceof LambdaExpr) {
            throw new UnsupportedOperationException();
        }

        if (argument instanceof MethodReferenceExpr) {
            throw new UnsupportedOperationException();
        }

        // - An explicitly typed lambda expression whose body is an expression that is not pertinent to applicability.

        if (argument instanceof LambdaExpr) {
            throw new UnsupportedOperationException();
        }

        // - An explicitly typed lambda expression whose body is a block, where at least one result expression is not
        //   pertinent to applicability.

        if (argument instanceof LambdaExpr) {
            throw new UnsupportedOperationException();
        }

        // - A parenthesized expression (§15.8.5) whose contained expression is not pertinent to applicability.

        if (argument instanceof EnclosedExpr) {
            EnclosedExpr enclosedExpr = (EnclosedExpr)argument;
            return isPertinentToApplicability(enclosedExpr.getInner());
        }

        // - A conditional expression (§15.25) whose second or third operand is not pertinent to applicability.

        if (argument instanceof ConditionalExpr) {
            ConditionalExpr conditionalExpr = (ConditionalExpr)argument;
            return isPertinentToApplicability(conditionalExpr.getThenExpr()) &&
                    isPertinentToApplicability(conditionalExpr.getElseExpr());
        }

        return true;
    }

    private Optional<ConstraintFormulaSet> testForApplicabilityByStrictInvocation(List<ResolvedType> Fs, List<Expression> es,
                                                                                  Substitution theta) {
        int n = Fs.size();
        int k = es.size();

        // If k ≠ n, or if there exists an i (1 ≤ i ≤ n) such that ei is pertinent to applicability (§15.12.2.2)
        // and either:
        // i) ei is a standalone expression of a primitive type but Fi is a reference type, or
        // ii) Fi is a primitive type but ei is not a standalone expression of a primitive type;
        if (k != n) {
            return Optional.empty();
        }
        for (int i=0;i<n;i++) {
            Expression ei = es.get(i);
            ResolvedType fi = Fs.get(i);
            if (isPertinentToApplicability(ei)) {
                if (ei.isStandaloneExpression() && JavaParserFacade.get(typeSolver).getType(ei).isPrimitive()
                        && fi.isReferenceType()) {
                    return Optional.empty();
                }
                if (fi.isPrimitive() && (!ei.isStandaloneExpression() || !JavaParserFacade.get(typeSolver).getType(ei).isPrimitive())) {
                    return Optional.empty();
                }
            }
        }
        // then the method is not applicable and there is no need to proceed with inference.
        //
        // Otherwise, C includes, for all i (1 ≤ i ≤ k) where ei is pertinent to applicability, ‹ei → Fi θ›.

        return Optional.of(constraintSetFromArgumentsSubstitution(Fs, es, theta, k));
    }

    private ResolvedType typeWithSubstitution(ResolvedType originalType, Substitution substitution) {
        return substitution.apply(originalType);
    }

    private Optional<ConstraintFormulaSet> testForApplicabilityByLooseInvocation(List<ResolvedType> Fs, List<Expression> es,
                                                                                 Substitution theta) {
        int n = Fs.size();
        int k = es.size();

        // If k ≠ n, the method is not applicable and there is no need to proceed with inference.

        if (k != n) {
            return Optional.empty();
        }

        // Otherwise, C includes, for all i (1 ≤ i ≤ k) where ei is pertinent to applicability, ‹ei → Fi θ›.
        return Optional.of(constraintSetFromArgumentsSubstitution(Fs, es, theta, k));
    }

    private ConstraintFormulaSet constraintSetFromArgumentsSubstitution(List<ResolvedType> Fs, List<Expression> es, Substitution theta, int k) {
        ConstraintFormulaSet constraintFormulaSet = ConstraintFormulaSet.empty();
        for (int i=0;i<k;i++) {
            Expression ei = es.get(i);
            ResolvedType fi = Fs.get(i);
            ResolvedType fiTheta = typeWithSubstitution(fi, theta);
            constraintFormulaSet = constraintFormulaSet.withConstraint(
                    new ExpressionCompatibleWithType(typeSolver, ei, fiTheta));
        }
        return constraintFormulaSet;
    }

    private Optional<ConstraintFormulaSet> testForApplicabilityByVariableArityInvocation(List<ResolvedType> Fs, List<Expression> es,
                                                                                         Substitution theta) {
        int k = es.size();

        // Let F'1, ..., F'k be the first k variable arity parameter types of m (§15.12.2.4). C includes,
        // for all i (1 ≤ i ≤ k) where ei is pertinent to applicability, ‹ei → F'i θ›.

        List<ResolvedType> FsFirst = new LinkedList<>();
        for (int i=0;i<k;i++) {
            ResolvedType FFirstI = i < Fs.size() ? Fs.get(i) : Fs.get(Fs.size() - 1);
            FsFirst.add(FFirstI);
        }

        return Optional.of(constraintSetFromArgumentsSubstitution(FsFirst, es, theta, k));
    }
}
