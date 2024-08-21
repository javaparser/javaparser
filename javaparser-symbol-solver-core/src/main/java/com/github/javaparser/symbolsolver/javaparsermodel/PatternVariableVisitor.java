/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.visitor.GenericVisitorWithDefaults;
import java.util.*;

public class PatternVariableVisitor extends GenericVisitorWithDefaults<PatternVariableResult, Void> {

    @Override
    public PatternVariableResult defaultAction(Node node, Void unused) {
        return new PatternVariableResult();
    }

    @Override
    public PatternVariableResult visit(BinaryExpr expression, Void unused) {
        if (expression.getOperator().equals(BinaryExpr.Operator.AND)) {
            return getVariablesIntroducedByAnd(expression);
        }
        if (expression.getOperator().equals(BinaryExpr.Operator.OR)) {
            return getVariablesIntroducedByOr(expression);
        }

        return new PatternVariableResult();
    }

    /**
     * The following rules apply to a conditional-and expression a && b:
     * - A pattern variable is introduced by a && b when true iff either
     *   (i) it is introduced by a when true or
     *   (ii) it is introduced by b when true.
     *
     * It should be noted that there is no rule for introducing a pattern variable by a && b when false.
     * This is because it cannot be determined at compile time which operand will evaluate to false.
     *
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.1
     */
    private static PatternVariableResult getVariablesIntroducedByAnd(BinaryExpr expression) {
        PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
        PatternVariableResult introducedByLeft = expression.getLeft().accept(variableVisitor, null);
        PatternVariableResult introducedByRight = expression.getRight().accept(variableVisitor, null);

        introducedByLeft.addVariablesIntroducedIfTrue(introducedByRight.getVariablesIntroducedIfTrue());
        introducedByLeft.clearVariablesIntroducedIfFalse();

        return introducedByLeft;
    }

    /**
     * The following rules apply to a conditional-or expression a || b:
     * - A pattern variable is introduced by a || b when false iff either
     *   (i) it is introduced by a when false or
     *   (ii) it is introduced by b when false.
     *
     * It should be noted that there is no rule for introducing a pattern variable by a || b when true.
     * This is because it cannot be determined at compile time which operand will evaluate to true.
     *
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.2
     */
    private static PatternVariableResult getVariablesIntroducedByOr(BinaryExpr expression) {
        PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
        PatternVariableResult introducedByLeft = expression.getLeft().accept(variableVisitor, null);
        PatternVariableResult introducedByRight = expression.getRight().accept(variableVisitor, null);

        introducedByLeft.addVariablesIntroducedIfFalse(introducedByRight.getVariablesIntroducedIfFalse());
        introducedByLeft.clearVariablesIntroducedIfTrue();

        return introducedByLeft;
    }

    @Override
    public PatternVariableResult visit(UnaryExpr expr, Void unused) {
        if (expr.getOperator().equals(UnaryExpr.Operator.LOGICAL_COMPLEMENT)) {
            return getVariablesIntroducedByLogicalComplement(expr);
        }

        return new PatternVariableResult();
    }

    /**
     *  The following rules apply to a logical complement expression !a:
     *  - A pattern variable is introduced by !a when true iff it is introduced by a when false.
     *  - A pattern variable is introduced by !a when false iff it is introduced by a when true.
     *
     *  https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.3
     */
    private static PatternVariableResult getVariablesIntroducedByLogicalComplement(UnaryExpr unaryExpr) {
        PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
        PatternVariableResult introducedByChild = unaryExpr.getExpression().accept(variableVisitor, null);

        introducedByChild.swapTrueAndFalse();

        return introducedByChild;
    }

    /**
     * The following rule applies to an instanceof expression with a pattern operand, a instanceof p:
     * - A pattern variable is introduced by a instanceof p when true iff the pattern p contains a declaration of the pattern variable.
     *
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.5
     */
    public PatternVariableResult visit(InstanceOfExpr instanceOfExpr, Void unused) {
        LinkedList<TypePatternExpr> variablesIntroducedIfTrue = new LinkedList<>();
        LinkedList<TypePatternExpr> variablesIntroducedIfFalse = new LinkedList<>();

        instanceOfExpr.getPattern().ifPresent(patternExpr -> {
            Queue<PatternExpr> patternQueue = new ArrayDeque<>();
            patternQueue.add(patternExpr);

            while (!patternQueue.isEmpty()) {
                PatternExpr toCheck = patternQueue.remove();
                if (toCheck.isTypePatternExpr()) {
                    variablesIntroducedIfTrue.add(toCheck.asTypePatternExpr());
                } else if (toCheck.isRecordPatternExpr()) {
                    patternQueue.addAll(toCheck.asRecordPatternExpr().getPatternList());
                } else {
                    throw new IllegalStateException("Found illegal pattern type in InstanceOf"
                            + toCheck.getClass().getCanonicalName());
                }
            }
        });

        return new PatternVariableResult(variablesIntroducedIfTrue, variablesIntroducedIfFalse);
    }

    /**
     * The following rules apply to a parenthesized expression (a):
     * - A pattern variable is introduced by (a) when true iff it is introduced by a when true.
     * - A pattern variable is introduced by (a) when false iff it is introduced by a when false.
     *
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.7
     */
    public PatternVariableResult visit(EnclosedExpr enclosedExpr, Void unused) {
        return enclosedExpr.getInner().accept(this, unused);
    }
}
