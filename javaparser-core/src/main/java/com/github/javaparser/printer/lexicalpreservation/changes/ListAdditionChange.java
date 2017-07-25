package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;

/**
 * The Addition of an element to a list.
 */
public class ListAdditionChange implements Change {
    private final ObservableProperty observableProperty;
    private final int index;
    private final Node nodeAdded;

    public ListAdditionChange(ObservableProperty observableProperty, int index, Node nodeAdded) {
        this.observableProperty = observableProperty;
        this.index = index;
        this.nodeAdded = nodeAdded;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            NodeList<Node> nodeList = new NodeList<>();
            Object currentRawValue = new NoChange().getValue(property, node);
            if (!(currentRawValue instanceof NodeList)){
                throw new IllegalStateException("Expected NodeList, found " + currentRawValue.getClass().getCanonicalName());
            }
            NodeList<?> currentNodeList = (NodeList<?>)(currentRawValue);
            nodeList.addAll(currentNodeList);
            nodeList.add(index, nodeAdded);
            return nodeList;
        } else {
            return new NoChange().getValue(property, node);
        }
    }
}
