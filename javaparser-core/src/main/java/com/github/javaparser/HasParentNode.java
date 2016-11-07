package com.github.javaparser;

import com.github.javaparser.ast.Node;

import java.util.List;

/**
 * An object that has a parent node.
 */
public interface HasParentNode<T> {

    // TODO nullable
    /**
     * Return the parent node or null, if no parent is set.
     */
    Node getParentNode();

    /**
     * Set the parent node.
     *
     * @param parentNode the parent node or null, to set no parent
     * @return return <i>this</i>
     */
    T setParentNode(Node parentNode);

    /**
     * <i>this</i> for everything except NodeLists. NodeLists use their parent as their children parent.
     */
    Node getParentNodeForChildren();

    /**
     * Get the ancestor of the node having the given type, or null if no ancestor of the given type is found.
     */
    default <N> N getAncestorOfType(Class<N> classType) {
        Node parent = getParentNode();
        while (parent != null) {
            if (classType.isAssignableFrom(parent.getClass())) {
                return classType.cast(parent);
            }
            parent = parent.getParentNode();
        }
        return null;
    }

    // TODO should become protected once Java lets us
    default void setAsParentNodeOf(List<? extends Node> childNodes) {
        if (childNodes != null) {
            for (HasParentNode current : childNodes) {
                current.setParentNode(getParentNodeForChildren());
            }
        }
    }

    // TODO should become protected once Java lets us
    default void setAsParentNodeOf(Node childNode) {
        if (childNode != null) {
            childNode.setParentNode(getParentNodeForChildren());
        }
    }

}
