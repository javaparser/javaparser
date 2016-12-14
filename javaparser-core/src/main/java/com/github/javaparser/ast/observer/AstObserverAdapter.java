package com.github.javaparser.ast.observer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

public abstract class AstObserverAdapter implements AstObserver {

    @Override
    public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
        // do nothing
    }

    @Override
    public void parentChange(Node observedNode, Node previousParent, Node newParent) {
        // do nothing
    }

    @Override
    public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
        // do nothing
    }
}
