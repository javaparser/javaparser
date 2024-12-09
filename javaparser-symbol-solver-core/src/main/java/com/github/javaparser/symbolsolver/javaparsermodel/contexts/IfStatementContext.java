/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.NormalCompletionVisitor;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableResult;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableVisitor;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

public class IfStatementContext extends StatementContext<IfStmt> {

    public IfStatementContext(IfStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    /**
     * The following rules apply to a statement if (e) S:
     * - A pattern variable introduced by e when true is definitely matched at S.
     *
     *  The following rules apply to a statement if (e) S else T:
     *  - A pattern variable introduced by e when true is definitely matched at S.
     *  - A pattern variable introduced by e when false is definitely matched at T.
     *
     *  https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2.2
     */
    @Override
    public List<TypePatternExpr> typePatternExprsExposedToChild(Node child) {
        PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
        List<TypePatternExpr> results = new LinkedList<>();

        Expression condition = wrappedNode.getCondition();
        PatternVariableResult patternsInScope = condition.accept(variableVisitor, null);

        boolean givenNodeIsWithinThenStatement = wrappedNode.getThenStmt().containsWithinRange(child);
        if (givenNodeIsWithinThenStatement) {
            results.addAll(patternsInScope.getVariablesIntroducedIfTrue());
        }

        wrappedNode.getElseStmt().ifPresent(elseStatement -> {
            boolean givenNodeIsWithinElseStatement = elseStatement.containsWithinRange(child);
            if (givenNodeIsWithinElseStatement) {
                results.addAll(patternsInScope.getVariablesIntroducedIfFalse());
            }
        });

        return results;
    }

    /**
     * The following rules apply to a statement if (e) S:
     * - A pattern variable is introduced by if (e) S iff
     *   (i) it is introduced by e when false and
     *   (ii) S cannot complete normally.
     *
     * The following rules apply to a statement if (e) S else T:
     * - A pattern variable is introduced by if (e) S else T iff either:
     *   - It is introduced by e when true, and S can complete normally, and T cannot complete normally; or
     *   - It is introduced by e when false, and S cannot complete normally, and T can complete normally.
     */
    @Override
    public List<TypePatternExpr> getIntroducedTypePatterns() {
        PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
        Expression condition = wrappedNode.getCondition();
        PatternVariableResult patternsInScope = condition.accept(variableVisitor, null);

        NormalCompletionVisitor completionVisitor = new NormalCompletionVisitor();
        boolean thenCanCompleteNormally = wrappedNode.getThenStmt().accept(completionVisitor, null);
        // If there is no else block, then we can treat it as an empty block which can complete normally by definition
        boolean elseCanCompleteNormally = !wrappedNode.getElseStmt().isPresent()
                || wrappedNode.getElseStmt().get().accept(completionVisitor, null);

        if (thenCanCompleteNormally && !elseCanCompleteNormally) {
            return patternsInScope.getVariablesIntroducedIfTrue();
        }

        if (!thenCanCompleteNormally && elseCanCompleteNormally) {
            return patternsInScope.getVariablesIntroducedIfFalse();
        }

        return Collections.emptyList();
    }

    /**
     * <pre>{@code
     * if() {
     *     // Does not match here (doesn't need to, as stuff inside of the if() is likely in context..)
     * } else if() {
     *     // Matches here
     * } else {
     *     // Matches here
     * }
     * }</pre>
     *
     * @return true, If this is an if inside of an if...
     */
    public boolean nodeContextIsChainedIfElseIf(Context parentContext) {
        return parentContext instanceof AbstractJavaParserContext
                && ((AbstractJavaParserContext<?>) this).getWrappedNode() instanceof IfStmt
                && ((AbstractJavaParserContext<?>) parentContext).getWrappedNode() instanceof IfStmt;
    }

    /**
     * <pre>{@code
     * if() {
     *     // Does not match here (doesn't need to, as stuff inside of the if() is likely in context..)
     * } else {
     *     // Does not match here, as the else block is a field inside of an ifstmt as opposed to child
     * }
     * }</pre>
     *
     * @return true, If this is an else inside of an if...
     */
    public boolean nodeContextIsImmediateChildElse(Context parentContext) {
        if (!(parentContext instanceof AbstractJavaParserContext)) {
            return false;
        }
        if (!(this instanceof AbstractJavaParserContext)) {
            return false;
        }

        AbstractJavaParserContext<?> abstractContext = (AbstractJavaParserContext<?>) this;
        AbstractJavaParserContext<?> abstractParentContext = (AbstractJavaParserContext<?>) parentContext;

        Node wrappedNode = abstractContext.getWrappedNode();
        Node wrappedParentNode = abstractParentContext.getWrappedNode();

        if (wrappedParentNode instanceof IfStmt) {
            IfStmt parentIfStmt = (IfStmt) wrappedParentNode;
            if (parentIfStmt.getElseStmt().isPresent()) {
                boolean currentNodeIsAnElseBlock = parentIfStmt.getElseStmt().get() == wrappedNode;
                if (currentNodeIsAnElseBlock) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * <pre>{@code
     * if() {
     *     // Does not match here (doesn't need to, as stuff inside of the if() is likely in context..)
     * } else {
     *     // Does not match here, as the else block is a field inside of an ifstmt as opposed to child
     * }
     * }</pre>
     *
     * @return true, If this is an else inside of an if...
     */
    public boolean nodeContextIsThenOfIfStmt(Context parentContext) {
        if (!(parentContext instanceof AbstractJavaParserContext)) {
            return false;
        }
        if (!(this instanceof AbstractJavaParserContext)) {
            return false;
        }

        AbstractJavaParserContext<?> abstractContext = (AbstractJavaParserContext<?>) this;
        AbstractJavaParserContext<?> abstractParentContext = (AbstractJavaParserContext<?>) parentContext;

        Node wrappedNode = abstractContext.getWrappedNode();
        Node wrappedParentNode = abstractParentContext.getWrappedNode();

        if (wrappedParentNode instanceof IfStmt) {
            IfStmt parentIfStmt = (IfStmt) wrappedParentNode;
            boolean currentNodeIsAnElseBlock = parentIfStmt.getThenStmt() == wrappedNode;
            if (currentNodeIsAnElseBlock) {
                return true;
            }
        }

        return false;
    }

    public boolean nodeContextIsConditionOfIfStmt(Context parentContext) {
        if (!(parentContext instanceof AbstractJavaParserContext)) {
            return false;
        }
        if (!(this instanceof AbstractJavaParserContext)) {
            return false;
        }

        AbstractJavaParserContext<?> abstractContext = (AbstractJavaParserContext<?>) this;
        AbstractJavaParserContext<?> abstractParentContext = (AbstractJavaParserContext<?>) parentContext;

        Node wrappedNode = abstractContext.getWrappedNode();
        Node wrappedParentNode = abstractParentContext.getWrappedNode();

        if (wrappedParentNode instanceof IfStmt) {
            IfStmt parentIfStmt = (IfStmt) wrappedParentNode;
            boolean currentNodeIsCondition = parentIfStmt.getCondition() == wrappedNode;
            if (currentNodeIsCondition) {
                return true;
            }
        }

        return false;
    }
}
