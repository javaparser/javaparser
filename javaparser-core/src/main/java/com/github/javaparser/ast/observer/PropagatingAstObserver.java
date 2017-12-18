/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.ast.observer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

/**
 * This AstObserver attach itself to all new nodes added to the nodes already observed.
 */
public abstract class PropagatingAstObserver implements AstObserver {

    /**
     * Wrap a given observer to make it self-propagating. If the given observer is an instance of PropagatingAstObserver
     * the observer is returned without changes.
     */
    public static PropagatingAstObserver transformInPropagatingObserver(final AstObserver observer) {
        if (observer instanceof PropagatingAstObserver) {
            return (PropagatingAstObserver) observer;
        }
        return new PropagatingAstObserver() {
            @Override
            public void concretePropertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                observer.propertyChange(observedNode, property, oldValue, newValue);
            }

            @Override
            public void concreteListChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                observer.listChange(observedNode, type, index, nodeAddedOrRemoved);
            }

            @Override
            public void parentChange(Node observedNode, Node previousParent, Node newParent) {
                observer.parentChange(observedNode, previousParent, newParent);
            }
        };
    }

    @Override
    public final void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
        considerRemoving(oldValue);
        considerAdding(newValue);
        concretePropertyChange(observedNode, property, oldValue, newValue);
    }

    @Override
    public final void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
        if (type == ListChangeType.REMOVAL) {
            considerRemoving(nodeAddedOrRemoved);
        } else if (type == ListChangeType.ADDITION) {
            considerAdding(nodeAddedOrRemoved);
        }
        concreteListChange(observedNode, type, index, nodeAddedOrRemoved);
    }

    @Override
    public void listReplacement(NodeList observedNode, int index, Node oldNode, Node newNode) {
        if (oldNode == newNode) {
            return;
        }
        considerRemoving(oldNode);
        considerAdding(newNode);
        concreteListReplacement(observedNode, index, oldNode, newNode);
    }

    public void concretePropertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
        // do nothing
    }

    public void concreteListChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
        // do nothing
    }

    public void concreteListReplacement(NodeList observedNode, int index, Node oldValue, Node newValue) {
        // do nothing
    }

    @Override
    public void parentChange(Node observedNode, Node previousParent, Node newParent) {
        // do nothing
    }

    private void considerRemoving(Object element) {
        if (element instanceof Observable) {
            if (((Observable) element).isRegistered(this)) {
                ((Observable) element).unregister(this);
            }
        }
    }

    private void considerAdding(Object element) {
        if (element instanceof Node) {
            ((Node) element).registerForSubtree(this);
        } else if (element instanceof Observable) {
            ((Observable) element).register(this);
        }
    }

}
