package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;

import java.util.Optional;

/**
 * The change in value of a property.
 */
public class PropertyChange implements Change {
    private ObservableProperty property;
    private Object oldValue;
    private Object newValue;

    public ObservableProperty getProperty() {
        return property;
    }

    public Object getOldValue() {
        return oldValue;
    }

    public Object getNewValue() {
        return newValue;
    }

    public PropertyChange(ObservableProperty property, Object oldValue, Object newValue) {
        this.property = property;
        this.oldValue = oldValue;
        this.newValue = newValue;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == this.property) {
            return newValue;
        } else {
            return property.getRawValue(node);
        }
    }
}
