package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.changes.*;

import java.util.*;

class LexicalDifferenceCalculator {

    /**
     * The ConcreteSyntaxModel represents the general format. This model is a calculated version of the ConcreteSyntaxModel,
     * with no condition, no lists, just tokens and node children.
     */
    static class CalculatedSyntaxModel {
        List<CsmElement> elements;

        CalculatedSyntaxModel(List<CsmElement> elements) {
            this.elements = elements;
        }

        public CalculatedSyntaxModel from(int index) {
            List<CsmElement> newList = new LinkedList<>();
            newList.addAll(elements.subList(index, elements.size()));
            return new CalculatedSyntaxModel(newList);
        }

        @Override
        public String toString() {
            return "CalculatedSyntaxModel{" +
                    "elements=" + elements +
                    '}';
        }

        public CalculatedSyntaxModel sub(int start, int end) {
            return new CalculatedSyntaxModel(elements.subList(start, end));
        }
    }

    static class CsmChild implements CsmElement {
        private Node child;

        public Node getChild() {
            return child;
        }

        public CsmChild(Node child) {
            this.child = child;
        }

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            throw new UnsupportedOperationException();
        }

        @Override
        public String toString() {
            return "child(" + child.getClass().getSimpleName()+")";
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            CsmChild csmChild = (CsmChild) o;

            return child.equals(csmChild.child);
        }

        @Override
        public int hashCode() {
            return child.hashCode();
        }
    }

    Difference calculateListRemovalDifference(ObservableProperty observableProperty, NodeList nodeList, int index, Node nodeRemoved) {
        Node container = nodeList.getParentNodeForChildren();
        CsmElement element = ConcreteSyntaxModel.forClass(container.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, container);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterListRemoval(element, observableProperty, nodeList, index, nodeRemoved);
        return Difference.calculate(original, after);
    }

    Difference calculateListAdditionDifference(ObservableProperty observableProperty, NodeList nodeList, int index, Node nodeAdded) {
        Node container = nodeList.getParentNodeForChildren();
        CsmElement element = ConcreteSyntaxModel.forClass(container.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, container);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterListAddition(element, observableProperty, nodeList, index, nodeAdded);
        return Difference.calculate(original, after);
    }

    Difference calculateListReplacementDifference(ObservableProperty observableProperty, NodeList nodeList, int index, Node oldValue, Node newValue) {
        Node container = nodeList.getParentNodeForChildren();
        CsmElement element = ConcreteSyntaxModel.forClass(container.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, container);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterListReplacement(element, observableProperty, nodeList, index, oldValue, newValue);
        return Difference.calculate(original, after);
    }

    public void calculatePropertyChange(NodeText nodeText, Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
        if (nodeText == null) {
            throw new NullPointerException();
        }
        CsmElement element = ConcreteSyntaxModel.forClass(observedNode.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, observedNode);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterPropertyChange(element, observedNode, property, oldValue, newValue);
        Difference difference = Difference.calculate(original, after);
        difference.apply(nodeText, observedNode);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelForNode(CsmElement csm, Node node) {
        List<CsmElement> elements = new LinkedList<>();
        calculatedSyntaxModelForNode(csm, node, elements, new NoChange());
        return new CalculatedSyntaxModel(elements);
    }

    CalculatedSyntaxModel calculatedSyntaxModelForNode(Node node) {
        return calculatedSyntaxModelForNode(ConcreteSyntaxModel.forClass(node.getClass()), node);
    }

    private void calculatedSyntaxModelForNode(CsmElement csm, Node node, List<CsmElement> elements, Change change) {
        if (csm instanceof CsmSequence) {
            CsmSequence csmSequence = (CsmSequence) csm;
            csmSequence.getElements().forEach(e -> calculatedSyntaxModelForNode(e, node, elements, change));
        } else if (csm instanceof CsmComment) {
            // nothing to do
        } else if (csm instanceof CsmSingleReference) {
            CsmSingleReference csmSingleReference = (CsmSingleReference)csm;
            Node child;
            if (change instanceof PropertyChange && ((PropertyChange)change).getProperty() == csmSingleReference.getProperty()) {
                child = (Node)((PropertyChange)change).getNewValue();
            } else {
                child = csmSingleReference.getProperty().getValueAsSingleReference(node);
            }
            if (child != null) {
                elements.add(new CsmChild(child));
            }
        } else if (csm instanceof CsmNone) {
            // nothing to do
        } else if (csm instanceof CsmToken) {
            elements.add(csm);
        } else if (csm instanceof CsmOrphanCommentsEnding) {
            // nothing to do
        } else if (csm instanceof CsmList) {
            CsmList csmList = (CsmList) csm;
            if (csmList.getProperty().isAboutNodes()) {
                NodeList nodeList = (NodeList)change.getValue(csmList.getProperty(), node);
                if (!nodeList.isEmpty()) {
                    calculatedSyntaxModelForNode(csmList.getPreceeding(), node, elements, change);
                    for (int i = 0; i < nodeList.size(); i++) {
                        if (i != 0) {
                            calculatedSyntaxModelForNode(csmList.getSeparatorPre(), node, elements, change);
                        }
                        elements.add(new CsmChild(nodeList.get(i)));
                        if (i != (nodeList.size() - 1)) {
                            calculatedSyntaxModelForNode(csmList.getSeparatorPost(), node, elements, change);
                        }

                    }
                    calculatedSyntaxModelForNode(csmList.getFollowing(), node, elements, change);
                }
            } else {
                Collection collection = (Collection) change.getValue(csmList.getProperty(), node);
                if (!collection.isEmpty()) {
                    calculatedSyntaxModelForNode(csmList.getPreceeding(), node, elements, change);

                    boolean first = true;
                    for (Iterator it = collection.iterator(); it.hasNext(); ) {
                        if (!first) {
                            calculatedSyntaxModelForNode(csmList.getSeparatorPre(), node, elements, change);
                        };
                        Object value = it.next();
                        if (value instanceof Modifier) {
                            Modifier modifier = (Modifier)value;
                            elements.add(new CsmToken(toToken(modifier)));
                        } else {
                            throw new UnsupportedOperationException(it.next().getClass().getSimpleName());
                        }
                        if (it.hasNext()) {
                            calculatedSyntaxModelForNode(csmList.getSeparatorPost(), node, elements, change);
                        }
                        first = false;
                    }
                    calculatedSyntaxModelForNode(csmList.getFollowing(), node, elements, change);
                }
            }
        } else if (csm instanceof CsmConditional) {
            CsmConditional csmConditional = (CsmConditional) csm;
            boolean satisfied = change.evaluate(csmConditional, node);
            if (satisfied) {
                calculatedSyntaxModelForNode(csmConditional.getThenElement(), node, elements, change);
            } else {
                calculatedSyntaxModelForNode(csmConditional.getElseElement(), node, elements, change);
            }
        } else if (csm instanceof CsmIndent) {
            //elements.add(csm);
        } else if (csm instanceof CsmUnindent) {
            //elements.add(csm);
        } else if (csm instanceof CsmAttribute) {
            CsmAttribute csmAttribute = (CsmAttribute)csm;
            Object value = change.getValue(csmAttribute.getProperty(), node);
            elements.add(new CsmToken(csmAttribute.getTokenType(value.toString()), value.toString()));
        } else {
            throw new UnsupportedOperationException(csm.getClass().getSimpleName());
        }
    }

    private int toToken(Modifier modifier) {
        switch (modifier) {
            case PUBLIC:
                return GeneratedJavaParserConstants.PUBLIC;
            case PRIVATE:
                return GeneratedJavaParserConstants.PRIVATE;
            case PROTECTED:
                return GeneratedJavaParserConstants.PROTECTED;
            case STATIC:
                return GeneratedJavaParserConstants.STATIC;
            default:
                throw new UnsupportedOperationException(modifier.name());
        }
    }

    ///
    /// Methods that calculate CalculatedSyntaxModel
    ///

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterPropertyChange(Node node, ObservableProperty property, Object oldValue, Object newValue) {
        return calculatedSyntaxModelAfterPropertyChange(ConcreteSyntaxModel.forClass(node.getClass()), node, property, oldValue, newValue);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterPropertyChange(CsmElement csm, Node node, ObservableProperty property, Object oldValue, Object newValue) {
        List<CsmElement> elements = new LinkedList<CsmElement>();
        calculatedSyntaxModelForNode(csm, node, elements, new PropertyChange(property, oldValue, newValue));
        return new CalculatedSyntaxModel(elements);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListRemoval(CsmElement csm, ObservableProperty observableProperty, NodeList nodeList, int index, Node nodeRemoved) {
        List<CsmElement> elements = new LinkedList<>();
        Node container = nodeList.getParentNodeForChildren();
        calculatedSyntaxModelForNode(csm, container, elements, new ListRemovalChange(observableProperty, nodeList, index, nodeRemoved));
        return new CalculatedSyntaxModel(elements);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListAddition(CsmElement csm, ObservableProperty observableProperty, NodeList nodeList, int index, Node nodeAdded) {
        List<CsmElement> elements = new LinkedList<>();
        Node container = nodeList.getParentNodeForChildren();
        calculatedSyntaxModelForNode(csm, container, elements, new ListAdditionChange(observableProperty, nodeList, index, nodeAdded));
        return new CalculatedSyntaxModel(elements);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListAddition(Node container, ObservableProperty observableProperty, int index, Node nodeAdded) {
        CsmElement csm = ConcreteSyntaxModel.forClass(container.getClass());
        NodeList nodeList = (NodeList)observableProperty.getRawValue(container);
        return calculatedSyntaxModelAfterListAddition(csm, observableProperty, nodeList, index, nodeAdded);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListRemoval(Node container, ObservableProperty observableProperty, int index, Node nodeRemoved) {
        CsmElement csm = ConcreteSyntaxModel.forClass(container.getClass());
        NodeList nodeList = (NodeList)observableProperty.getRawValue(container);
        return calculatedSyntaxModelAfterListRemoval(csm, observableProperty, nodeList, index, nodeRemoved);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListReplacement(CsmElement csm, ObservableProperty observableProperty, NodeList nodeList, int index, Node oldValue, Node newValue) {
        List<CsmElement> elements = new LinkedList<>();
        Node container = nodeList.getParentNodeForChildren();
        calculatedSyntaxModelForNode(csm, container, elements, new ListReplacementChange(observableProperty, nodeList, index, oldValue, newValue));
        return new CalculatedSyntaxModel(elements);
    }

}
