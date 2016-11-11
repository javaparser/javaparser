package com.github.javaparser.ast.observing;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

public interface ListObserver<N extends Node> {
    void listChange(NodeList<N> observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved);
}
