/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.TextBlockLiteralExpr;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.Stringable;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.changes.*;
import com.github.javaparser.utils.LineSeparator;

import java.util.*;

class LexicalDifferenceCalculator {

    /**
     * The ConcreteSyntaxModel represents the general format. This model is a calculated version of the ConcreteSyntaxModel,
     * with no condition, no lists, just tokens and node children.
     */
    static class CalculatedSyntaxModel {

        final List<CsmElement> elements;

        CalculatedSyntaxModel(List<CsmElement> elements) {
            this.elements = elements;
        }

        public CalculatedSyntaxModel from(int index) {
            return new CalculatedSyntaxModel(new ArrayList<>(elements.subList(index, elements.size())));
        }

        @Override
        public String toString() {
            return "CalculatedSyntaxModel{" + "elements=" + elements + '}';
        }

        CalculatedSyntaxModel sub(int start, int end) {
            return new CalculatedSyntaxModel(elements.subList(start, end));
        }

        void removeIndentationElements() {
            elements.removeIf(el -> el instanceof CsmIndent || el instanceof CsmUnindent);
        }
    }

    static class CsmChild implements CsmElement {

        private final Node child;

        public Node getChild() {
            return child;
        }

        CsmChild(Node child) {
            this.child = child;
        }

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            throw new UnsupportedOperationException();
        }

        @Override
        public String toString() {
            return "child(" + child.getClass().getSimpleName() + ")";
        }

        @Override
        public boolean equals(Object o) {
            if (this == o)
                return true;
            if (o == null || getClass() != o.getClass())
                return false;
            CsmChild csmChild = (CsmChild) o;
            return child.equals(csmChild.child);
        }

        @Override
        public int hashCode() {
            return child.hashCode();
        }
    }

    List<DifferenceElement> calculateListRemovalDifference(ObservableProperty observableProperty, NodeList<?> nodeList, int index) {
        Node container = nodeList.getParentNodeForChildren();
        CsmElement element = ConcreteSyntaxModel.forClass(container.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, container);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterListRemoval(element, observableProperty, nodeList, index);
        return DifferenceElementCalculator.calculate(original, after);
    }

    List<DifferenceElement> calculateListAdditionDifference(ObservableProperty observableProperty, NodeList<?> nodeList, int index, Node nodeAdded) {
        Node container = nodeList.getParentNodeForChildren();
        CsmElement element = ConcreteSyntaxModel.forClass(container.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, container);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterListAddition(element, observableProperty, nodeList, index, nodeAdded);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(original, after);
        // Set the line separator character tokens
        LineSeparator lineSeparator = container.getLineEndingStyleOrDefault(LineSeparator.SYSTEM);
        replaceEolTokens(differenceElements, lineSeparator);
        return differenceElements;
    }

    /*
     * Replace EOL token in the list of {@code DifferenceElement} by the specified line separator
     */
    private void replaceEolTokens(List<DifferenceElement> differenceElements, LineSeparator lineSeparator) {
        CsmElement eol = getNewLineToken(lineSeparator);
        for (int i = 0; i < differenceElements.size(); i++) {
            DifferenceElement differenceElement = differenceElements.get(i);
            differenceElements.set(i, differenceElement.replaceEolTokens(eol));
        }
    }

    /*
     * Returns a new line token 
     */
    private CsmElement getNewLineToken(LineSeparator lineSeparator) {
        return CsmElement.newline(lineSeparator);
    }

    List<DifferenceElement> calculateListReplacementDifference(ObservableProperty observableProperty, NodeList<?> nodeList, int index, Node newValue) {
        Node container = nodeList.getParentNodeForChildren();
        CsmElement element = ConcreteSyntaxModel.forClass(container.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, container);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterListReplacement(element, observableProperty, nodeList, index, newValue);
        return DifferenceElementCalculator.calculate(original, after);
    }

    void calculatePropertyChange(NodeText nodeText, Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
        if (nodeText == null) {
            throw new NullPointerException();
        }
        CsmElement element = ConcreteSyntaxModel.forClass(observedNode.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, observedNode);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterPropertyChange(element, observedNode, property, oldValue, newValue);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(original, after);
        Difference difference = new Difference(differenceElements, nodeText, observedNode);
        difference.apply();
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
            CsmSingleReference csmSingleReference = (CsmSingleReference) csm;
            Node child;
            if (change instanceof PropertyChange && ((PropertyChange) change).getProperty() == csmSingleReference.getProperty()) {
                child = (Node) ((PropertyChange) change).getNewValue();
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
                Object rawValue = change.getValue(csmList.getProperty(), node);
                NodeList<?> nodeList;
                if (rawValue instanceof Optional) {
                    Optional<?> optional = (Optional<?>) rawValue;
                    if (optional.isPresent()) {
                        if (!(optional.get() instanceof NodeList)) {
                            throw new IllegalStateException("Expected NodeList, found " + optional.get().getClass().getCanonicalName());
                        }
                        nodeList = (NodeList<?>) optional.get();
                    } else {
                        nodeList = new NodeList<>();
                    }
                } else {
                    if (!(rawValue instanceof NodeList)) {
                        throw new IllegalStateException("Expected NodeList, found " + rawValue.getClass().getCanonicalName());
                    }
                    nodeList = (NodeList<?>) rawValue;
                }
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
                Collection<?> collection = (Collection<?>) change.getValue(csmList.getProperty(), node);
                if (!collection.isEmpty()) {
                    calculatedSyntaxModelForNode(csmList.getPreceeding(), node, elements, change);
                    boolean first = true;
                    for (Iterator<?> it = collection.iterator(); it.hasNext(); ) {
                        if (!first) {
                            calculatedSyntaxModelForNode(csmList.getSeparatorPre(), node, elements, change);
                        }
                        Object value = it.next();
                        if (value instanceof Modifier) {
                            Modifier modifier = (Modifier) value;
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
            elements.add(csm);
        } else if (csm instanceof CsmUnindent) {
            elements.add(csm);
        } else if (csm instanceof CsmAttribute) {
            CsmAttribute csmAttribute = (CsmAttribute) csm;
            Object value = change.getValue(csmAttribute.getProperty(), node);
            String text = value.toString();
            if (value instanceof Stringable) {
                text = ((Stringable) value).asString();
            }
            elements.add(new CsmToken(csmAttribute.getTokenType(node, value.toString(), text), text));
        } else if ((csm instanceof CsmString) && (node instanceof StringLiteralExpr)) {
            // fix #2382:
            // This method calculates the syntax model _after_ the change has been applied.
            // If the given change is a PropertyChange, the returned model should
            // contain the new value, otherwise the original/current value should be used.
            if (change instanceof PropertyChange) {
                elements.add(new CsmToken(GeneratedJavaParserConstants.STRING_LITERAL, "\"" + ((PropertyChange) change).getNewValue() + "\""));
            } else {
                elements.add(new CsmToken(GeneratedJavaParserConstants.STRING_LITERAL, "\"" + ((StringLiteralExpr) node).getValue() + "\""));
            }
        } else if ((csm instanceof CsmString) && (node instanceof TextBlockLiteralExpr)) {
            // FIXME: csm should be CsmTextBlock -- See also #2677
            if (change instanceof PropertyChange) {
                elements.add(new CsmToken(GeneratedJavaParserConstants.TEXT_BLOCK_LITERAL, "\"\"\"" + ((PropertyChange) change).getNewValue() + "\"\"\""));
            } else {
                elements.add(new CsmToken(GeneratedJavaParserConstants.TEXT_BLOCK_LITERAL, "\"\"\"" + ((TextBlockLiteralExpr) node).getValue() + "\"\"\""));
            }
        } else if ((csm instanceof CsmChar) && (node instanceof CharLiteralExpr)) {
            if (change instanceof PropertyChange) {
                elements.add(new CsmToken(GeneratedJavaParserConstants.CHAR, "'" + ((PropertyChange) change).getNewValue() + "'"));
            } else {
                elements.add(new CsmToken(GeneratedJavaParserConstants.CHAR, "'" + ((CharLiteralExpr) node).getValue() + "'"));
            }
        } else if (csm instanceof CsmMix) {
            CsmMix csmMix = (CsmMix) csm;
            List<CsmElement> mixElements = new LinkedList<>();
            csmMix.getElements().forEach(e -> calculatedSyntaxModelForNode(e, node, mixElements, change));
            elements.add(new CsmMix(mixElements));
        } else if (csm instanceof CsmChild) {
            elements.add(csm);
        } else {
            throw new UnsupportedOperationException(csm.getClass().getSimpleName() + " " + csm);
        }
    }

    public static int toToken(Modifier modifier) {
        switch(modifier.getKeyword()) {
            case PUBLIC:
                return GeneratedJavaParserConstants.PUBLIC;
            case PRIVATE:
                return GeneratedJavaParserConstants.PRIVATE;
            case PROTECTED:
                return GeneratedJavaParserConstants.PROTECTED;
            case STATIC:
                return GeneratedJavaParserConstants.STATIC;
            case FINAL:
                return GeneratedJavaParserConstants.FINAL;
            case ABSTRACT:
                return GeneratedJavaParserConstants.ABSTRACT;
            case TRANSIENT:
                return GeneratedJavaParserConstants.TRANSIENT;
            case SYNCHRONIZED:
                return GeneratedJavaParserConstants.SYNCHRONIZED;
            case VOLATILE:
                return GeneratedJavaParserConstants.VOLATILE;
            case NATIVE:
                return GeneratedJavaParserConstants.NATIVE;
            case STRICTFP:
                return GeneratedJavaParserConstants.STRICTFP;
            case TRANSITIVE:
                return GeneratedJavaParserConstants.TRANSITIVE;
            default:
                throw new UnsupportedOperationException(modifier.getKeyword().name());
        }
    }

    // /
    // / Methods that calculate CalculatedSyntaxModel
    // /
    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterPropertyChange(Node node, ObservableProperty property, Object oldValue, Object newValue) {
        return calculatedSyntaxModelAfterPropertyChange(ConcreteSyntaxModel.forClass(node.getClass()), node, property, oldValue, newValue);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterPropertyChange(CsmElement csm, Node node, ObservableProperty property, Object oldValue, Object newValue) {
        List<CsmElement> elements = new LinkedList<>();
        calculatedSyntaxModelForNode(csm, node, elements, new PropertyChange(property, oldValue, newValue));
        return new CalculatedSyntaxModel(elements);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListRemoval(CsmElement csm, ObservableProperty observableProperty, NodeList<?> nodeList, int index) {
        List<CsmElement> elements = new LinkedList<>();
        Node container = nodeList.getParentNodeForChildren();
        calculatedSyntaxModelForNode(csm, container, elements, new ListRemovalChange(observableProperty, index));
        return new CalculatedSyntaxModel(elements);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListAddition(CsmElement csm, ObservableProperty observableProperty, NodeList<?> nodeList, int index, Node nodeAdded) {
        List<CsmElement> elements = new LinkedList<>();
        Node container = nodeList.getParentNodeForChildren();
        calculatedSyntaxModelForNode(csm, container, elements, new ListAdditionChange(observableProperty, index, nodeAdded));
        return new CalculatedSyntaxModel(elements);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListAddition(Node container, ObservableProperty observableProperty, int index, Node nodeAdded) {
        CsmElement csm = ConcreteSyntaxModel.forClass(container.getClass());
        Object rawValue = observableProperty.getRawValue(container);
        if (!(rawValue instanceof NodeList)) {
            throw new IllegalStateException("Expected NodeList, found " + rawValue.getClass().getCanonicalName());
        }
        NodeList<?> nodeList = (NodeList<?>) rawValue;
        return calculatedSyntaxModelAfterListAddition(csm, observableProperty, nodeList, index, nodeAdded);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterListRemoval(Node container, ObservableProperty observableProperty, int index) {
        CsmElement csm = ConcreteSyntaxModel.forClass(container.getClass());
        Object rawValue = observableProperty.getRawValue(container);
        if (!(rawValue instanceof NodeList)) {
            throw new IllegalStateException("Expected NodeList, found " + rawValue.getClass().getCanonicalName());
        }
        NodeList<?> nodeList = (NodeList<?>) rawValue;
        return calculatedSyntaxModelAfterListRemoval(csm, observableProperty, nodeList, index);
    }

    // Visible for testing
    private CalculatedSyntaxModel calculatedSyntaxModelAfterListReplacement(CsmElement csm, ObservableProperty observableProperty, NodeList<?> nodeList, int index, Node newValue) {
        List<CsmElement> elements = new LinkedList<>();
        Node container = nodeList.getParentNodeForChildren();
        calculatedSyntaxModelForNode(csm, container, elements, new ListReplacementChange(observableProperty, index, newValue));
        return new CalculatedSyntaxModel(elements);
    }
}
