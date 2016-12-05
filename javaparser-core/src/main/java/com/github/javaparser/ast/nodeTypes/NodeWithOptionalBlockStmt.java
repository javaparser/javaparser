package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.stmt.BlockStmt;

import java.util.Optional;

public interface NodeWithOptionalBlockStmt<N extends Node> {
    Optional<BlockStmt> getBody();

    N setBody(BlockStmt block);

    default BlockStmt createBody() {
        BlockStmt block = new BlockStmt();
        setBody(block);
        block.setParentNode((Node) this);

        return block;
    }
}
