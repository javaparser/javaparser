package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;

/**
 * The replacement of an element in a list.
 */
public class ListReplacementChange implements Change {
    private ObservableProperty observableProperty;
    private int index;
    private Node newValue;

    public ListReplacementChange(ObservableProperty observableProperty, int index, Node newValue) {
        this.observableProperty = observableProperty;
        this.index = index;
        this.newValue = newValue;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            NodeList<Node> nodeList = new NodeList<>();
            NodeList<Node> currentNodeList = (NodeList<Node>)(new NoChange().getValue(property, node));
            nodeList.addAll(currentNodeList);
            nodeList.set(index, newValue);
            return nodeList;
        } else {
            return new NoChange().getValue(property, node);
        }
    }
}
