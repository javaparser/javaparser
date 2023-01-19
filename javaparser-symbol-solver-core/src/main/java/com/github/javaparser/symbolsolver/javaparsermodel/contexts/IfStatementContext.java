/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;

import java.util.ArrayList;
import java.util.List;

public class IfStatementContext extends StatementContext<IfStmt> {
//public class IfStatementContext extends AbstractJavaParserContext<IfStmt> {

    public IfStatementContext(IfStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }


    @Override
    public List<PatternExpr> patternExprsExposedToChild(Node child) {
        Expression condition = wrappedNode.getCondition();
        Context conditionContext = JavaParserFactory.getContext(condition, typeSolver);

        List<PatternExpr> results = new ArrayList<>();

        boolean givenNodeIsWithinThenStatement = wrappedNode.getThenStmt().containsWithinRange(child);
        if(givenNodeIsWithinThenStatement) {
            results.addAll(conditionContext.patternExprsExposedFromChildren());
        }

        wrappedNode.getElseStmt().ifPresent(elseStatement -> {
            boolean givenNodeIsWithinElseStatement = elseStatement.containsWithinRange(child);
            if(givenNodeIsWithinElseStatement) {
                results.addAll(conditionContext.negatedPatternExprsExposedFromChildren());
            }
        });

        return results;
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
