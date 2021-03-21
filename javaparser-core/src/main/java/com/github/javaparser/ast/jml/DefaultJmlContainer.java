package com.github.javaparser.ast.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.SimpleName;

/**
 * @author Alexander Weigl
 * @version 1 (3/21/21)
 */
public class DefaultJmlContainer implements JmlContainer {
    @Override
    public NodeList getElements() {
        return null;
    }

    @Override
    public Node setElements(NodeList elements) {
        return null;
    }

    @Override
    public NodeList<SimpleName> getJmlTags() {
        return null;
    }

    @Override
    public boolean isSingleLine() {
        return false;
    }

    @Override
    public Node setSingleLine(boolean singleLine) {
        return null;
    }

    @Override
    public Node setJmlTags(NodeList jmlTags) {
        return null;
    }
}
