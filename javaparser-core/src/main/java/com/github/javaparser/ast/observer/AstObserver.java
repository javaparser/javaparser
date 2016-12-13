package com.github.javaparser.ast.observer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

/**
 * An Observer for an AST element (either a Node or a NodeList).
 */
public interface AstObserver {

    /**
     * Type of change occurring on a List
     */
    public enum ListChangeType {
        ADDITION,
        REMOVAL
    }

    /**
     * The value of a property is changed
     *
     * @param observedNode owner of the property
     * @param property property changed
     * @param oldValue value of the property before the change
     * @param newValue value of the property after the change
     */
    void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue);

    /**
     * The parent of a node is changed
     *
     * @param observedNode node of which the parent is changed
     * @param previousParent previous parent
     * @param newParent new parent
     */
    void parentChange(Node observedNode, Node previousParent, Node newParent);

    /**
     * A list is changed
     *
     * @param observedNode list changed
     * @param type type of change
     * @param index position at which the changed occurred
     * @param nodeAddedOrRemoved element added or removed
     */
    void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved);
}
