package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.changes.Change;
import com.github.javaparser.printer.lexicalpreservation.changes.NoChange;
import com.github.javaparser.printer.lexicalpreservation.changes.PropertyChange;

import java.util.*;

public class LexicalDifferenceCalculator {

    class CalculatedSyntaxModel {
        List<CsmElement> elements;

        public CalculatedSyntaxModel(List<CsmElement> elements) {
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

    public void calculatePropertyChange(NodeText nodeText, Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
        // CompilationUnit
        // PACKAGE_DECLARATION
        // oldValue -> aPackage
        CsmElement element = ConcreteSyntaxModel.forClass(observedNode.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelFor(element, observedNode);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterPropertyChange(element, observedNode, property, oldValue, newValue);
        Difference difference = Difference.calculate(original, after);
        System.out.println("DIFFERENCE " + difference);
        difference.apply(nodeText);
    }

    private CalculatedSyntaxModel calculatedSyntaxModelFor(CsmElement csm, Node node) {
        List<CsmElement> elements = new LinkedList<CsmElement>();
        calculatedSyntaxModelFor(csm, node, elements, new NoChange());
        return new CalculatedSyntaxModel(elements);
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
    }

    public static boolean isWhitespace(int tokenType) {
        return tokenType == 0 || tokenType == 3 || tokenType == 1 || tokenType == 32 || tokenType == 31;
    }

    public static boolean isWhitespace(CsmElement csmElement) {
        return csmElement instanceof CsmToken && isWhitespace(((CsmToken)csmElement).getTokenType());
    }

    private void calculatedSyntaxModelFor(CsmElement csm, Node node, List<CsmElement> elements, Change change) {
        if (csm instanceof CsmSequence) {
            CsmSequence csmSequence = (CsmSequence) csm;
            csmSequence.getElements().forEach(e -> calculatedSyntaxModelFor(e, node, elements, change));
        } else if (csm instanceof CsmComment) {
            // nothing to do
        } else if (csm instanceof CsmSingleReference) {
            CsmSingleReference csmSingleReference = (CsmSingleReference)csm;
            Node child;
            if (change instanceof PropertyChange && ((PropertyChange)change).getProperty() == csmSingleReference.getProperty()) {
                child = (Node)((PropertyChange)change).getNewValue();
            } else {
                child = csmSingleReference.getProperty().singlePropertyFor(node);
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
                NodeList nodeList = csmList.getProperty().listValueFor(node);
                if (!nodeList.isEmpty()) {
                    calculatedSyntaxModelFor(csmList.getPreceeding(), node, elements, change);
                    for (int i = 0; i < nodeList.size(); i++) {
                        if (i != 0) {
                            calculatedSyntaxModelFor(csmList.getSeparatorPre(), node, elements, change);
                        }
                        elements.add(new CsmChild(nodeList.get(i)));
                        if (i != (nodeList.size() - 1)) {
                            calculatedSyntaxModelFor(csmList.getSeparatorPost(), node, elements, change);
                        }

                    }
                    calculatedSyntaxModelFor(csmList.getFollowing(), node, elements, change);
                }
            } else {
                Collection collection = csmList.getProperty().listPropertyFor(node);
                if (!collection.isEmpty()) {
                    calculatedSyntaxModelFor(csmList.getPreceeding(), node, elements, change);

                    boolean first = true;
                    for (Iterator it = collection.iterator(); it.hasNext(); ) {
                        if (!first) {
                            calculatedSyntaxModelFor(csmList.getSeparatorPre(), node, elements, change);
                        };
                        Object value = it.next();
                        if (value instanceof Modifier) {
                            Modifier modifier = (Modifier)value;
                            elements.add(new CsmToken(toToken(modifier)));
                        } else {
                            throw new UnsupportedOperationException(it.next().getClass().getSimpleName());
                        }
                        //findCompulsoryTokens(it.next());
                        if (it.hasNext()) {
                            calculatedSyntaxModelFor(csmList.getSeparatorPost(), node, elements, change);
                        }
                        first = false;
                    }
                    calculatedSyntaxModelFor(csmList.getFollowing(), node, elements, change);
                }
            }
        } else if (csm instanceof CsmConditional) {
            CsmConditional csmConditional = (CsmConditional) csm;
            boolean satisfied = change.evaluate(csmConditional, node);
            if (satisfied) {
                calculatedSyntaxModelFor(csmConditional.getThenElement(), node, elements, change);
            } else {
                calculatedSyntaxModelFor(csmConditional.getElseElement(), node, elements, change);
            }
        } else if (csm instanceof CsmIndent) {
            // nothing to do
        } else if (csm instanceof CsmUnindent) {
            // nothing to do
        } else {
            throw new UnsupportedOperationException(csm.getClass().getSimpleName());
        }
    }

    private int toToken(Modifier modifier) {
        switch (modifier) {
            case PUBLIC:
                return ASTParserConstants.PUBLIC;
            default:
                throw new UnsupportedOperationException();
        }
    }

    private CalculatedSyntaxModel calculatedSyntaxModelAfterPropertyChange(CsmElement csm, Node node, ObservableProperty property, Object oldValue, Object newValue) {
        List<CsmElement> elements = new LinkedList<CsmElement>();
        calculatedSyntaxModelFor(csm, node, elements, new PropertyChange(property, oldValue, newValue));
        return new CalculatedSyntaxModel(elements);
    }

}
