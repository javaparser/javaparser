package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;

public interface NodeWithBody<N extends Node> {
    Statement getBody();

    N setBody(final Statement body);

    default BlockStmt createBlockStatementAsBody() {
        BlockStmt b = new BlockStmt();
        b.setParentNode((Node) this);
        setBody(b);
        return b;
    }
}
