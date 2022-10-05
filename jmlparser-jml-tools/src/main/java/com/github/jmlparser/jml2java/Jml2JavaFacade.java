package com.github.jmlparser.jml2java;

import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.utils.Pair;

import java.util.Stack;

/**
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
public class Jml2JavaFacade {
    public static Pair<BlockStmt, Expression> translate(Expression expression) {
        Jml2JavaTranslator j2jt = new Jml2JavaTranslator();
        BlockStmt result = new BlockStmt();
        var e = j2jt.accept(expression, result);
        return new Pair<>(result, e);
    }

    public BlockStmt translate(JmlContract expression) {
        Jml2JavaTranslator j2jt = new Jml2JavaTranslator();
        BlockStmt result = new BlockStmt();
        return result;
    }

    public static boolean containsJmlExpression(Expression expression) {
        Stack<Expression> search = new Stack<>();
        search.add(expression);

        while (!search.isEmpty()) {
            Expression e = search.pop();
            if (e instanceof Jmlish) {
                return true;
            }

            if (e instanceof BinaryExpr be) {
                if (be.getOperator() == BinaryExpr.Operator.IMPLICATION)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.RIMPLICATION)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.EQUIVALENCE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUB_LOCK)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUB_LOCKE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUBTYPE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.RANGE)
                    return true;
            }

            for (Node childNode : e.getChildNodes()) {
                if (childNode instanceof Expression ex)
                    search.add(ex);
            }
        }
        return false;
    }
}
