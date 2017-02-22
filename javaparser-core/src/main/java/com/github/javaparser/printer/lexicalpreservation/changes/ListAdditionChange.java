package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;

/**
 * The Addition of an element to a list.
 */
public class ListAdditionChange implements Change {
    private ObservableProperty observableProperty;
    private NodeList nodeList;
    private int index;
    private Node nodeAdded;

    public ListAdditionChange(ObservableProperty observableProperty, NodeList nodeList, int index, Node nodeAdded) {
        this.observableProperty = observableProperty;
        this.nodeList = nodeList;
        this.index = index;
        this.nodeAdded = nodeAdded;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            NodeList nodeList = new NodeList();
            NodeList currentNodeList = (NodeList)(new NoChange().getValue(property, node));
            nodeList.addAll(currentNodeList);
            nodeList.add(index, nodeAdded);
            return nodeList;
        } else {
            return new NoChange().getValue(property, node);
        }
    }
}
