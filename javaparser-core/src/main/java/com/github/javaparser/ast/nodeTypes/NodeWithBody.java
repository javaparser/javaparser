package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;

public interface NodeWithBody<T> {
    public Statement getBody();

    public T setBody(final Statement body);

    public default BlockStmt createBlockStatementAsBody() {
        BlockStmt b = new BlockStmt();
        b.setParentNode((Node) this);
        setBody(b);
        return b;
    }
}
