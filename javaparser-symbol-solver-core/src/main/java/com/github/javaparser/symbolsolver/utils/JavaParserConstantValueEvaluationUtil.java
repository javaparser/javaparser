/*
 *
 *  * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 *  * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *  *
 *  * This file is part of JavaParser.
 *  *
 *  * JavaParser can be used either under the terms of
 *  * a) the GNU Lesser General Public License as published by
 *  *     the Free Software Foundation, either version 3 of the License, or
 *  *     (at your option) any later version.
 *  * b) the terms of the Apache License
 *  *
 *  * You should have received a copy of both licenses in LICENCE.LGPL and
 *  * LICENCE.APACHE. Please refer to those files for details.
 *  *
 *  * JavaParser is distributed in the hope that it will be useful,
 *  * but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  * GNU Lesser General Public License for more details.
 *
 */

package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ast.Modifier.Keyword;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedAnnotation;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnnotation;

import java.math.BigDecimal;
import java.util.Optional;

public class JavaParserConstantValueEvaluationUtil {

    /**
     * Tries to evaluate the expression to a constant value.
     * That can be a {@link String}, a {@link Boolean}, any {@link Number}, a {@link ResolvedEnumConstantDeclaration}, a {@link ResolvedAnnotation} or a {@link ResolvedType}.
     */
    public static Object evaluateConstantExpression(Expression expression, TypeSolver typeSolver) {
        if (expression.isBooleanLiteralExpr()) {
            return expression.asBooleanLiteralExpr().getValue();
        } else if (expression.isDoubleLiteralExpr()) {
            return expression.asDoubleLiteralExpr().asDouble();
        } else if (expression.isIntegerLiteralExpr()) {
            return expression.asIntegerLiteralExpr().asNumber();
        } else if (expression.isLongLiteralExpr()) {
            return expression.asLongLiteralExpr().asNumber();
        } else if (expression.isCharLiteralExpr()) {
            return expression.asCharLiteralExpr().asChar();
        } else if (expression.isStringLiteralExpr()) {
            return expression.asStringLiteralExpr().getValue();
        } else if (expression.isClassExpr()) {
            return expression.asClassExpr().getType().resolve();
        } else if (expression.isAnnotationExpr()) {
            return new JavaParserAnnotation(expression.asAnnotationExpr(), typeSolver);
        } else if (expression.isArrayInitializerExpr()) {
            return expression.asArrayInitializerExpr().getValues().stream().map(it -> evaluateConstantExpression(it, typeSolver)).toArray();
        } else if (expression.isFieldAccessExpr()) {
            ResolvedValueDeclaration tempResolvedFieldAccess = expression.asFieldAccessExpr().resolve();
            if (tempResolvedFieldAccess.isEnumConstant()) {
                return tempResolvedFieldAccess.asEnumConstant();
            } else if (tempResolvedFieldAccess.isField() && tempResolvedFieldAccess.asField().hasModifier(Keyword.STATIC) && tempResolvedFieldAccess.asField().hasModifier(Keyword.FINAL)) {
                return tempResolvedFieldAccess.asField().constantValue();
            }
        } else if (expression.isNullLiteralExpr()) {
            return null;
        } else if (expression.isNameExpr()) {
            ResolvedValueDeclaration tempResolvedFieldAccess = expression.asNameExpr().resolve();
            if (tempResolvedFieldAccess.isEnumConstant()) {
                return tempResolvedFieldAccess.asEnumConstant();
            } else if (tempResolvedFieldAccess.isField() && tempResolvedFieldAccess.asField().hasModifier(Keyword.STATIC) && tempResolvedFieldAccess.asField().hasModifier(Keyword.FINAL)) {
                ResolvedFieldDeclaration tempField = tempResolvedFieldAccess.asField();
                Optional<Expression> tempInitializer = tempField.toAst(FieldDeclaration.class).flatMap(fieldDecl -> fieldDecl.getVariables().stream()
                        .filter(it -> it.getNameAsString().equals(tempField.getName()))
                        .findFirst()).flatMap(VariableDeclarator::getInitializer);
                if (tempInitializer.isPresent()) {
                    return evaluateConstantExpression(tempInitializer.get(), typeSolver);
                } else {
                    return tempField.constantValue();
                }
            }
        } else if (expression.isBinaryExpr()) {
            Expression tempLeftExpr = expression.asBinaryExpr().getLeft();
            Expression tempRightExpr = expression.asBinaryExpr().getRight();
            BinaryExpr.Operator tempOperator = expression.asBinaryExpr().getOperator();
            Object tempLeft = evaluateConstantExpression(tempLeftExpr, typeSolver);
            Object tempRight = evaluateConstantExpression(tempRightExpr, typeSolver);
            return combineValuesWith(tempLeft, tempRight, tempOperator);
        } else if (expression.isUnaryExpr()) {
            Expression tempExpression = expression.asUnaryExpr().getExpression();
            UnaryExpr.Operator tempOperator = expression.asUnaryExpr().getOperator();
            Object tempResult = evaluateConstantExpression(tempExpression, typeSolver);
            switch (tempOperator) {
                case PLUS:
                    if(tempResult instanceof Number) {
                        return tempResult;
                    }
                    break;
                case MINUS:
                    if(tempResult instanceof Number) {
                        return new BigDecimal(tempResult.toString()).multiply(new BigDecimal(-1));
                    }
                    break;
                case LOGICAL_COMPLEMENT:
                    if (tempResult instanceof Boolean) {
                        return !(boolean) tempResult;
                    }
                    break;
            }
        }
        throw new IllegalStateException("Currently can not evaluate expressions of type " + expression.getClass().getName() + ": " + expression);
    }

    private static Object combineValuesWith(Object left, Object right, BinaryExpr.Operator operator) {
        int i = 5 | 10;

        switch (operator) {
            case OR:
            case AND:
                return combineAsBoolean(left, right, operator);
            case PLUS:
                return combinePlus(left, right);
        }

        throw new UnsupportedOperationException("Currently can not evaluate binary expression with operator " + operator.asString());
    }

    private static Object combinePlus(Object left, Object right) {
        if (left instanceof Number && right instanceof Number) {
            return new BigDecimal(left.toString()).add(new BigDecimal(right.toString()));
        } else if (left instanceof String || right instanceof String) {
            return String.valueOf(left) + right;

        } else {
            throw new IllegalStateException("can not combine non Number and not String values (left: " + left + ", right: " + right + ") with +");
        }
    }

    private static boolean combineAsBoolean(Object left, Object right, BinaryExpr.Operator operator) {
        if (!(left instanceof Boolean) || !(right instanceof Boolean)) {
            throw new IllegalStateException("Can not combine non boolean values (left: " + left + ", right: " + right + ") with " + operator.asString());
        }
        if (operator == BinaryExpr.Operator.AND) {
            return (boolean) left && (boolean) right;
        } else if (operator == BinaryExpr.Operator.OR) {
            return (boolean) left || (boolean) right;
        } else {
            throw new IllegalStateException("Can not combine boolean values with the operator " + operator.asString());
        }
    }

    /**
     * Tries to evaluate the expression as ({@link JavaParserConstantValueEvaluationUtil#evaluateConstantExpression(Expression, TypeSolver)}).
     * Also, if the returned value is a number and the expectedType is given, tries to convert the result to the expected type.
     */
    public static Object evaluateConstantExpression(Expression expression, TypeSolver typeSolver, ResolvedType expectedType) {
        Object tempResult = evaluateConstantExpression(expression, typeSolver);

        if (tempResult instanceof Number && expectedType != null && expectedType.isReferenceType()) {
            Number tempNum = (Number) tempResult;
            String tempQualifiedName = expectedType.asReferenceType().getQualifiedName();
            try {
                Class<?> tempClass = Class.forName(tempQualifiedName);
                if (tempClass == float.class || tempClass == Float.class) {
                    return tempNum.floatValue();
                } else if (tempClass == double.class || tempClass == Double.class) {
                    return tempNum.doubleValue();
                } else if (tempClass == short.class || tempClass == Short.class) {
                    return tempNum.shortValue();
                } else if (tempClass == int.class || tempClass == Integer.class) {
                    return tempNum.intValue();
                } else if (tempClass == long.class || tempClass == Long.class) {
                    return tempNum.longValue();
                } else if (tempClass == byte.class || tempClass == Byte.class) {
                    return tempNum.byteValue();
                }
            } catch (Throwable ignore) {

            }
        }

        return tempResult;
    }
}
