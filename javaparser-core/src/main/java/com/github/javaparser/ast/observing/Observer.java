package com.github.javaparser.ast.observing;

import com.github.javaparser.ast.Node;

public interface Observer {
    <P> void propertyChange(Node observedNode, String propertyName, P oldValue, P newValue);
    void listChange(Node observedNode, String listName, ListChangeType type, int index, Node nodeAddedOrRemoved);
}
