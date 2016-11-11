package com.github.javaparser.ast.observing;

import com.github.javaparser.ast.Node;

public interface NodeObserver {
    <P> void propertyChange(Node observedNode, String propertyName, P oldValue, P newValue);
}
