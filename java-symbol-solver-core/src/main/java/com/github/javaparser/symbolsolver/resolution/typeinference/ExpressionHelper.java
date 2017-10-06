package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class ExpressionHelper {

    /**
     * See https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.2
     * @return
     */
    public static boolean isStandaloneExpression(Expression expression) {
        return !isPolyExpression(expression);
    }

    /**
     * See https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.2
     * @return
     */
    public static boolean isPolyExpression(Expression expression) {
        if (expression instanceof EnclosedExpr) {
            throw new UnsupportedOperationException(expression.toString());
        }
        if (expression instanceof ObjectCreationExpr) {
            // A class instance creation expression is a poly expression (§15.2) if it uses the diamond form for type
            // arguments to the class, and it appears in an assignment context or an invocation context (§5.2, §5.3).
            // Otherwise, it is a standalone expression.
            ObjectCreationExpr objectCreationExpr = (ObjectCreationExpr)expression;
            if (objectCreationExpr.isUsingDiamondOperator()) {
                throw new UnsupportedOperationException(expression.toString());
            } else {
                return false;
            }
        }
        if (expression instanceof MethodCallExpr) {
            MethodCallExpr methodCallExpr = (MethodCallExpr)expression;

            // A method invocation expression is a poly expression if all of the following are true:
            //
            // 1. The invocation appears in an assignment context or an invocation context (§5.2, §5.3).

            if (!appearsInAssignmentContext(expression) || appearsInInvocationContext(expression)) {
                return false;
            }

            // 2. If the invocation is qualified (that is, any form of MethodInvocation except for the first), then
            //    the invocation elides TypeArguments to the left of the Identifier.

            if (isQualified(methodCallExpr) && !elidesTypeArguments(methodCallExpr)) {
                return false;
            }

            // 3. The method to be invoked, as determined by the following subsections, is generic (§8.4.4) and has a
            //    return type that mentions at least one of the method's type parameters.

            //boolean condition3 =;
            throw new UnsupportedOperationException(expression.toString());

            // Otherwise, the method invocation expression is a standalone expression.
            //return true;
        }
        if (expression instanceof MethodReferenceExpr) {
            throw new UnsupportedOperationException(expression.toString());
        }
        if (expression instanceof ConditionalExpr) {
            throw new UnsupportedOperationException(expression.toString());
        }
        if (expression instanceof LambdaExpr) {
            return true;
        }
        return false;
    }

    private static boolean elidesTypeArguments(MethodCallExpr methodCall) {
        throw new UnsupportedOperationException();
    }

    private static boolean isQualified(MethodCallExpr methodCall) {
        throw new UnsupportedOperationException();
    }

    // Not sure if should look if the parent is an assignment context
    private static boolean appearsInAssignmentContext(Expression expression) {
        if (expression.getParentNode().isPresent()) {
            Node parent = expression.getParentNode().get();
            if (parent instanceof ExpressionStmt) {
                return false;
            }
            if (parent instanceof MethodCallExpr) {
                return false;
            }
            if (parent instanceof ReturnStmt) {
                return false;
            }
            throw new UnsupportedOperationException(parent.getClass().getCanonicalName());
        }
        return false;
    }

    private static boolean appearsInInvocationContext(Expression expression) {
        if (expression.getParentNode().isPresent()) {
            Node parent = expression.getParentNode().get();
            if (parent instanceof ExpressionStmt) {
                return false;
            }
            if (parent instanceof MethodCallExpr) {
                return true;
            }
            throw new UnsupportedOperationException(parent.getClass().getCanonicalName());
        }
        return false;
    }

    public static boolean isExplicitlyTyped(LambdaExpr lambdaExpr) {
        return lambdaExpr.getParameters().stream().allMatch(p -> !(p.getType() instanceof UnknownType));
    }

    public static List<Expression> getResultExpressions(BlockStmt blockStmt) {
        throw new UnsupportedOperationException();
    }

    public static boolean isCompatibleInAssignmentContext(Expression expression, ResolvedType type, TypeSolver typeSolver) {
        return type.isAssignableBy(JavaParserFacade.get(typeSolver).getType(expression, false));
    }
}
