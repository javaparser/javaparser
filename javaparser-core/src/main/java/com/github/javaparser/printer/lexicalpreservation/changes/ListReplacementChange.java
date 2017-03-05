package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;

/**
 * The replacement of an element in a list.
 */
public class ListReplacementChange implements Change {
    private ObservableProperty observableProperty;
    private NodeList nodeList;
    private int index;
    private Node oldValue;
    private Node newValue;

    public ListReplacementChange(ObservableProperty observableProperty, NodeList nodeList, int index, Node oldValue, Node newValue) {
        this.observableProperty = observableProperty;
        this.nodeList = nodeList;
        this.index = index;
        this.oldValue = oldValue;
        this.newValue = newValue;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            NodeList nodeList = new NodeList();
            NodeList currentNodeList = (NodeList)(new NoChange().getValue(property, node));
            nodeList.addAll(currentNodeList);
            nodeList.set(index, newValue);
            return nodeList;
        } else {
            return new NoChange().getValue(property, node);
        }
    }
}
