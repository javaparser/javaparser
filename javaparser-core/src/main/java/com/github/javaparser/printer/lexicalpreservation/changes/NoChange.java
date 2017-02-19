package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;

public class NoChange implements Change {

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        return property.getValue(node);
    }
}
