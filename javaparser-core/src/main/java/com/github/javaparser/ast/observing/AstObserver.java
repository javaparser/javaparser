package com.github.javaparser.ast.observing;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

public interface AstObserver {
    void propertyChange(Node observedNode, String propertyName, Object oldValue, Object newValue);
    void parentChange(Node observedNode, Node previousParent, Node newParent);
    void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved);
}
