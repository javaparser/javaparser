package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;

public interface NodeWithStatements<T> {
    NodeList<Statement> getStmts();

    T setStmts(final NodeList<Statement> stmts);

    @SuppressWarnings("unchecked")
    default T addStatement(Statement statement) {
        getStmts().add(statement);
        statement.setParentNode((Node) this);
        return (T) this;
    }

    @SuppressWarnings("unchecked")
    default T addStatement(int index, final Statement statement) {
        getStmts().add(index, statement);
        statement.setParentNode((Node) this);
        return (T) this;
    }

    default T addStatement(Expression expr) {
        ExpressionStmt statement = new ExpressionStmt(expr);
        expr.setParentNode(statement);
        return addStatement(statement);
    }

    default T addStatement(String statement) {
        return addStatement(new NameExpr(statement));
    }

    default T addStatement(int index, final Expression expr) {
        Statement stmt = new ExpressionStmt(expr);
        expr.setParentNode(stmt);
        return addStatement(index, stmt);
    }

    default <A extends Statement> A addAndGetStatement(A statement) {
        getStmts().add(statement);
        statement.setParentNode((Node) this);
        return statement;
    }

    default Statement addAndGetStatement(int index, final Statement statement) {
        getStmts().add(index, statement);
        statement.setParentNode((Node) this);
        return statement;
    }

    default ExpressionStmt addAndGetStatement(Expression expr) {
        ExpressionStmt statement = new ExpressionStmt(expr);
        expr.setParentNode(statement);
        return addAndGetStatement(statement);
    }

    default ExpressionStmt addAndGetStatement(String statement) {
        return addAndGetStatement(new NameExpr(statement));
    }
    
    default boolean isEmpty() {
        return getStmts().isEmpty();
    }
}
