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

package com.github.javaparser.symbolsolver.resolution.typeinference.constraintformulas;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typeinference.*;
import com.github.javaparser.utils.Pair;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isCompatibleInALooseInvocationContext;
import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isProperType;
import static java.util.stream.Collectors.toList;

/**
 * An expression is compatible in a loose invocation context with type T
 *
 * @author Federico Tomassetti
 */
public class ExpressionCompatibleWithType extends ConstraintFormula {
    private TypeSolver typeSolver;
    private Expression expression;
    private ResolvedType T;

    public ExpressionCompatibleWithType(TypeSolver typeSolver, Expression expression, ResolvedType T) {
        this.typeSolver = typeSolver;
        this.expression = expression;
        this.T = T;
    }

    @Override
    public ReductionResult reduce(BoundSet currentBoundSet) {
        // If T is a proper type, the constraint reduces to true if the expression is compatible in a loose
        // invocation context with T (§5.3), and false otherwise.

        if (isProperType(T)) {
            if (isCompatibleInALooseInvocationContext(typeSolver, expression, T)) {
                return ReductionResult.trueResult();
            }
            return ReductionResult.falseResult();
        }

        // Otherwise, if the expression is a standalone expression (§15.2) of type S, the constraint reduces
        // to ‹S → T›.

        if (expression.isStandaloneExpression()) {
            ResolvedType s = JavaParserFacade.get(typeSolver).getType(expression, false);
            return ReductionResult.empty().withConstraint(new TypeCompatibleWithType(typeSolver, s, T));
        }

        // Otherwise, the expression is a poly expression (§15.2). The result depends on the form of the expression:

        if (expression.isPolyExpression()) {

            // - If the expression is a parenthesized expression of the form ( Expression' ), the constraint reduces
            //   to ‹Expression' → T›.

            if (expression instanceof EnclosedExpr) {
                EnclosedExpr enclosedExpr = (EnclosedExpr)expression;
                return ReductionResult.oneConstraint(new ExpressionCompatibleWithType(typeSolver, enclosedExpr.getInner(), T));
            }

            // - If the expression is a class instance creation expression or a method invocation expression, the
            //   constraint reduces to the bound set B3 which would be used to determine the expression's invocation
            //   type when targeting T, as defined in §18.5.2. (For a class instance creation expression, the
            //   corresponding "method" used for inference is defined in §15.9.3).
            //
            //   This bound set may contain new inference variables, as well as dependencies between these new
            //   variables and the inference variables in T.

            if (expression instanceof ObjectCreationExpr) {
                BoundSet B3 = new TypeInference(typeSolver).invocationTypeInferenceBoundsSetB3();
                return ReductionResult.bounds(B3);
            }

            if (expression instanceof MethodCallExpr) {
                throw new UnsupportedOperationException();
            }

            // - If the expression is a conditional expression of the form e1 ? e2 : e3, the constraint reduces to two
            //   constraint formulas, ‹e2 → T› and ‹e3 → T›.

            if (expression instanceof ConditionalExpr) {
                ConditionalExpr conditionalExpr = (ConditionalExpr)expression;
                return ReductionResult.withConstraints(
                        new ExpressionCompatibleWithType(typeSolver, conditionalExpr.getThenExpr(), T),
                        new ExpressionCompatibleWithType(typeSolver, conditionalExpr.getElseExpr(), T));
            }

            // - If the expression is a lambda expression or a method reference expression, the result is specified
            //   below.

            // A constraint formula of the form ‹LambdaExpression → T›, where T mentions at least one inference variable, is reduced as follows:

            if (expression instanceof LambdaExpr) {
                LambdaExpr lambdaExpr = (LambdaExpr)expression;

                // - If T is not a functional interface type (§9.8), the constraint reduces to false.

                if (!FunctionalInterfaceLogic.isFunctionalInterfaceType(T)) {
                    return ReductionResult.falseResult();
                }

                // - Otherwise, let T' be the ground target type derived from T, as specified in §15.27.3. If §18.5.3
                //   is used to derive a functional interface type which is parameterized, then the test that
                //   F<A'1, ..., A'm> is a subtype of F<A1, ..., Am> is not performed (instead, it is asserted with a
                //   constraint formula below). Let the target function type for the lambda expression be the
                //   function type of T'. Then:

                Pair<ResolvedType, Boolean> result = TypeHelper.groundTargetTypeOfLambda(lambdaExpr, T, typeSolver);
                ResolvedType TFirst = result.a;
                MethodType targetFunctionType = TypeHelper.getFunctionType(TFirst);
                targetFunctionType = replaceTypeVariablesWithInferenceVariables(targetFunctionType);
                if (result.b) {
                    throw new UnsupportedOperationException();
                }

                //   - If no valid function type can be found, the constraint reduces to false.
                //
                //     Federico: THIS SHOULD NOT HAPPEN, IN CASE WE WILL THROW AN EXCEPTION
                //
                //   - Otherwise, the congruence of LambdaExpression with the target function type is asserted as
                //     follows:
                //
                //     - If the number of lambda parameters differs from the number of parameter types of the function
                //       type, the constraint reduces to false.

                if (targetFunctionType.getFormalArgumentTypes().size() != lambdaExpr.getParameters().size()) {
                    return ReductionResult.falseResult();
                }

                //     - If the lambda expression is implicitly typed and one or more of the function type's parameter
                //       types is not a proper type, the constraint reduces to false.
                //
                //       This condition never arises in practice, due to the handling of implicitly typed lambda
                //       expressions in §18.5.1 and the substitution applied to the target type in §18.5.2.

                //     - If the function type's result is void and the lambda body is neither a statement expression
                //       nor a void-compatible block, the constraint reduces to false.

                if (targetFunctionType.getReturnType().isVoid()) {
                    throw new UnsupportedOperationException();
                }

                //     - If the function type's result is not void and the lambda body is a block that is not
                //       value-compatible, the constraint reduces to false.

                if (!targetFunctionType.getReturnType().isVoid() && lambdaExpr.getBody() instanceof BlockStmt
                        && !isValueCompatibleBlock(lambdaExpr.getBody())) {
                    return ReductionResult.falseResult();
                }

                //     - Otherwise, the constraint reduces to all of the following constraint formulas:
                List<ConstraintFormula> constraints = new LinkedList<>();

                //       - If the lambda parameters have explicitly declared types F1, ..., Fn and the function type
                //         has parameter types G1, ..., Gn, then i) for all i (1 ≤ i ≤ n), ‹Fi = Gi›, and ii) ‹T' <: T›.

                boolean hasExplicitlyDeclaredTypes = lambdaExpr.getParameters().stream().anyMatch(p -> !(p.getType() instanceof UnknownType));
                if (hasExplicitlyDeclaredTypes) {
                    throw new UnsupportedOperationException();
                }

                //       - If the function type's return type is a (non-void) type R, assume the lambda's parameter
                //         types are the same as the function type's parameter types. Then:

                if (!targetFunctionType.getReturnType().isVoid()) {

                    ResolvedType R = targetFunctionType.getReturnType();

                    if (TypeHelper.isProperType(R)) {

                        //         - If R is a proper type, and if the lambda body or some result expression in the lambda body
                        //           is not compatible in an assignment context with R, then false.

                        if (lambdaExpr.getBody() instanceof BlockStmt) {
                            List<Expression> resultExpressions = ExpressionHelper.getResultExpressions((BlockStmt)lambdaExpr.getBody());
                            for (Expression e : resultExpressions) {
                                if (!ExpressionHelper.isCompatibleInAssignmentContext(e, R, typeSolver)) {
                                    return ReductionResult.falseResult();
                                }
                            }
                        } else {
                            Expression e = ((ExpressionStmt)lambdaExpr.getBody()).getExpression();
                            if (!ExpressionHelper.isCompatibleInAssignmentContext(e, R, typeSolver)) {
                                return ReductionResult.falseResult();
                            }
                        }
                    } else {
                        //         - Otherwise, if R is not a proper type, then where the lambda body has the form Expression,
                        //           the constraint ‹Expression → R›; or where the lambda body is a block with result
                        //           expressions e1, ..., em, for all i (1 ≤ i ≤ m), ‹ei → R›.

                        if (lambdaExpr.getBody() instanceof BlockStmt) {
                            getAllReturnExpressions((BlockStmt)lambdaExpr.getBody()).forEach(e -> constraints.add(new ExpressionCompatibleWithType(typeSolver, e, R)));
                        } else {
                            // FEDERICO: Added - Start
                            for (int i=0;i<lambdaExpr.getParameters().size();i++) {
                                ResolvedType paramType = targetFunctionType.getFormalArgumentTypes().get(i);
                                TypeInferenceCache.addRecord(typeSolver, lambdaExpr, lambdaExpr.getParameter(i).getNameAsString(), paramType);
                            }
                            // FEDERICO: Added - End
                            Expression e = ((ExpressionStmt)lambdaExpr.getBody()).getExpression();
                            constraints.add(new ExpressionCompatibleWithType(typeSolver, e, R));
                        }
                    }
                }

                return ReductionResult.withConstraints(constraints);
            }

            // A constraint formula of the form ‹MethodReference → T›, where T mentions at least one inference variable, is reduced as follows:

            if (expression instanceof MethodReferenceExpr) {

                // - If T is not a functional interface type, or if T is a functional interface type that does not have a function type (§9.9), the constraint reduces to false.
                //
                // - Otherwise, if there does not exist a potentially applicable method for the method reference when targeting T, the constraint reduces to false.
                //
                // - Otherwise, if the method reference is exact (§15.13.1), then let P1, ..., Pn be the parameter types of the function type of T, and let F1, ..., Fk be the parameter types of the potentially applicable method. The constraint reduces to a new set of constraints, as follows:
                //
                //   - In the special case where n = k+1, the parameter of type P1 is to act as the target reference of the invocation. The method reference expression necessarily has the form ReferenceType :: [TypeArguments] Identifier. The constraint reduces to ‹P1 <: ReferenceType› and, for all i (2 ≤ i ≤ n), ‹Pi → Fi-1›.
                //
                //     In all other cases, n = k, and the constraint reduces to, for all i (1 ≤ i ≤ n), ‹Pi → Fi›.
                //
                //   - If the function type's result is not void, let R be its return type. Then, if the result of the potentially applicable compile-time declaration is void, the constraint reduces to false. Otherwise, the constraint reduces to ‹R' → R›, where R' is the result of applying capture conversion (§5.1.10) to the return type of the potentially applicable compile-time declaration.
                //
                // - Otherwise, the method reference is inexact, and:
                //
                //   - If one or more of the function type's parameter types is not a proper type, the constraint reduces to false.
                //
                //     This condition never arises in practice, due to the handling of inexact method references in §18.5.1 and the substitution applied to the target type in §18.5.2.
                //
                //   - Otherwise, a search for a compile-time declaration is performed, as specified in §15.13.1. If there is no compile-time declaration for the method reference, the constraint reduces to false. Otherwise, there is a compile-time declaration, and:
                //
                //     - If the result of the function type is void, the constraint reduces to true.
                //
                //     - Otherwise, if the method reference expression elides TypeArguments, and the compile-time declaration is a generic method, and the return type of the compile-time declaration mentions at least one of the method's type parameters, then the constraint reduces to the bound set B3 which would be used to determine the method reference's invocation type when targeting the return type of the function type, as defined in §18.5.2. B3 may contain new inference variables, as well as dependencies between these new variables and the inference variables in T.
                //
                //     - Otherwise, let R be the return type of the function type, and let R' be the result of applying capture conversion (§5.1.10) to the return type of the invocation type (§15.12.2.6) of the compile-time declaration. If R' is void, the constraint reduces to false; otherwise, the constraint reduces to ‹R' → R›.

                throw new UnsupportedOperationException();
            }

            throw new RuntimeException("This should not happen");
        }

        throw new RuntimeException("This should not happen");
    }

    private List<Expression> getAllReturnExpressions(BlockStmt blockStmt) {
        return blockStmt.findAll(ReturnStmt.class).stream()
                .filter(r -> r.getExpression().isPresent())
                .map(r -> r.getExpression().get())
                .collect(toList());
    }

    private boolean isValueCompatibleBlock(Statement statement) {
        // A block lambda body is value-compatible if it cannot complete normally (§14.21) and every return statement
        // in the block has the form return Expression;.

        if (statement instanceof BlockStmt) {
            if (!ControlFlowLogic.getInstance().canCompleteNormally(statement)) {
                return true;
            }
            List<ReturnStmt> returnStmts = statement.findAll(ReturnStmt.class);
            return returnStmts.stream().allMatch(r -> r.getExpression().isPresent());
        }
        return false;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ExpressionCompatibleWithType that = (ExpressionCompatibleWithType) o;

        if (!typeSolver.equals(that.typeSolver)) return false;
        if (!expression.equals(that.expression)) return false;
        return T.equals(that.T);
    }

    @Override
    public int hashCode() {
        int result = typeSolver.hashCode();
        result = 31 * result + expression.hashCode();
        result = 31 * result + T.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "ExpressionCompatibleWithType{" +
                "typeSolver=" + typeSolver +
                ", expression=" + expression +
                ", T=" + T +
                '}';
    }

    private MethodType replaceTypeVariablesWithInferenceVariables(MethodType methodType) {
        // Find all type variable
        Map<ResolvedTypeVariable, InferenceVariable> correspondences = new HashMap<>();
        List<ResolvedType> newFormalArgumentTypes = new LinkedList<>();
        for (ResolvedType formalArg : methodType.getFormalArgumentTypes()) {
            newFormalArgumentTypes.add(replaceTypeVariablesWithInferenceVariables(formalArg, correspondences));
        }
        ResolvedType newReturnType = replaceTypeVariablesWithInferenceVariables(methodType.getReturnType(), correspondences);
        return new MethodType(methodType.getTypeParameters(), newFormalArgumentTypes, newReturnType, methodType.getExceptionTypes());
    }

    private ResolvedType replaceTypeVariablesWithInferenceVariables(ResolvedType originalType, Map<ResolvedTypeVariable, InferenceVariable> correspondences) {
        if (originalType.isTypeVariable()) {
            if (!correspondences.containsKey(originalType.asTypeVariable())) {
                correspondences.put(originalType.asTypeVariable(), InferenceVariable.unnamed(originalType.asTypeVariable().asTypeParameter()));
            }
            return correspondences.get(originalType.asTypeVariable());
        }
        if (originalType.isPrimitive()) {
            return originalType;
        }
        throw new UnsupportedOperationException(originalType.toString());
    }
}
