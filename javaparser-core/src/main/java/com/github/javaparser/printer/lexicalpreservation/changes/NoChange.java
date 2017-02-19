package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;

public class NoChange implements Change {

    @Override
    public boolean evaluate(CsmConditional csmConditional, Node node) {
        switch (csmConditional.getCondition()) {
            case FLAG:
                return (Boolean) csmConditional.getProperty().singleValueFor(node);
            case IS_NOT_EMPTY:
                return !csmConditional.getProperty().isNullOrEmpty(node);
            case IS_EMPTY:
                return csmConditional.getProperty().isNullOrEmpty(node);
            case IS_PRESENT:
                return !csmConditional.getProperty().isNullOrEmpty(node);
            default:
                throw new UnsupportedOperationException("" + csmConditional.getProperty() + " " + csmConditional.getCondition());
        }
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        return property.getValue(node);
    }
}
