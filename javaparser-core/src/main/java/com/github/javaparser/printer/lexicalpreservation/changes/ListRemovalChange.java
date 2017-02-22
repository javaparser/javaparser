package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;

/**
 * The removal of an element in a list.
 */
public class ListRemovalChange implements Change {
    private ObservableProperty observableProperty;
    private NodeList nodeList;
    private int index;
    private Node nodeRemoved;

    public ListRemovalChange(ObservableProperty observableProperty, NodeList nodeList, int index, Node nodeRemoved) {
        this.observableProperty = observableProperty;
        this.nodeList = nodeList;
        this.index = index;
        this.nodeRemoved = nodeRemoved;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            NodeList nodeList = new NodeList();
            NodeList currentNodeList = (NodeList)(new NoChange().getValue(property, node));
            nodeList.addAll(currentNodeList);
            nodeList.remove(index);
            return nodeList;
        } else {
            return new NoChange().getValue(property, node);
        }
    }
}
