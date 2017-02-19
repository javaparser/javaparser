package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;

public interface Change {

    default boolean evaluate(CsmConditional csmConditional, Node node) {
        switch (csmConditional.getCondition()) {
            case FLAG:
                return (Boolean) getValue(csmConditional.getProperty(), node);
            case IS_NOT_EMPTY:
                return !ObservableProperty.valueIsNullOrEmpty(getValue(csmConditional.getProperty(), node));
            case IS_EMPTY:
                return ObservableProperty.valueIsNullOrEmpty(getValue(csmConditional.getProperty(), node));
            case IS_PRESENT:
                return !ObservableProperty.valueIsNullOrEmpty(getValue(csmConditional.getProperty(), node));
            default:
                throw new UnsupportedOperationException("" + csmConditional.getProperty() + " " + csmConditional.getCondition());
        }
    }

    Object getValue(ObservableProperty property, Node node);
}
