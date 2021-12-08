package com.github.javaparser.ast.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * Temporary container for parsing artifacts of different kinds.
 *
 * @author Alexander Weigl
 * @version 1 (11/23/21)
 */
public class ArbitraryNodeContainer extends Node {
    private NodeList<Node> children;

    public ArbitraryNodeContainer() {
        this(new NodeList<>());
    }

    public ArbitraryNodeContainer(NodeList<Node> children) {
        super(null);
        this.children = children;
    }


    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }

    public NodeList<Node> getChildren() {
        return children;
    }

    public void setChildren(NodeList<Node> children) {
        this.children = children;
    }
}
