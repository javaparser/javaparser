package com.github.javaparser.ast.observing;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

public abstract class PropagatingAstObserver implements AstObserver {

    @Override
    public void propertyChange(Node observedNode, String propertyName, Object oldValue, Object newValue) {
        considerRemoving(oldValue);
        considerAdding(newValue);
        concretePropertyChange(observedNode, propertyName, oldValue, newValue);
    }

    @Override
    public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
        if (type == ListChangeType.REMOVAL) {
            considerRemoving(nodeAddedOrRemoved);
        } else if (type == ListChangeType.ADDITION) {
            considerAdding(nodeAddedOrRemoved);
        }
        concreteListChange(observedNode, type, index, nodeAddedOrRemoved);
    }

    protected abstract void concretePropertyChange(Node observedNode, String propertyName, Object oldValue, Object newValue);

    protected abstract void concreteListChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved);

    private void considerRemoving(Object element) {
        if (element instanceof Observable) {
            if (((Observable) element).isRegistered(this)) {
                ((Observable) element).unregister(this);
            }
        }
    }

    private void considerAdding(Object element) {
        if (element instanceof Observable) {
            ((Observable) element).register(this);
        }
    }

}
