package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.utils.Pair;

import java.util.Optional;

/**
 * The replacement of an element in a list.
 */
public class ListReplacementChange implements Change {
    private final ObservableProperty observableProperty;
    private final int index;
    private final Node newValue;

    public ListReplacementChange(ObservableProperty observableProperty, int index, Node newValue) {
        this.observableProperty = observableProperty;
        this.index = index;
        this.newValue = newValue;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            NodeList nodeList = new NodeList();
            Object currentRawValue = new NoChange().getValue(property, node);
            if (currentRawValue instanceof Optional) {
                Optional optional = (Optional)currentRawValue;
                currentRawValue = optional.orElseGet(null);
            }
            if (!(currentRawValue instanceof NodeList)){
                throw new IllegalStateException("Expected NodeList, found " + currentRawValue.getClass().getCanonicalName());
            }
            NodeList currentNodeList = (NodeList)currentRawValue;
            nodeList.addAll(currentNodeList);
            nodeList.set(index, newValue);
            return nodeList;
        } else {
            return new NoChange().getValue(property, node);
        }
    }
}
