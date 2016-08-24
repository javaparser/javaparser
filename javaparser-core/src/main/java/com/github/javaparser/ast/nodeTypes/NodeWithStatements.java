package com.github.javaparser.ast.nodeTypes;

import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;

public interface NodeWithStatements<T> {
    public List<Statement> getStmts();

    public T setStmts(final List<Statement> stmts);

    @SuppressWarnings("unchecked")
    public default T addStatement(Statement statement) {
        getStmts().add(statement);
        statement.setParentNode((Node)this);
        return (T) this;
    }

    public default T addStatement(String statement) {
        return addStatement(new ExpressionStmt(new NameExpr(statement)));
    }
}
