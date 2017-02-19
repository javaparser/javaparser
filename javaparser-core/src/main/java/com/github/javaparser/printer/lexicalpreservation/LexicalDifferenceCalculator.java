package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.changes.Change;
import com.github.javaparser.printer.lexicalpreservation.changes.NoChange;
import com.github.javaparser.printer.lexicalpreservation.changes.PropertyChange;

import java.util.*;

public class LexicalDifferenceCalculator {

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

    public void calculatePropertyChange(NodeText nodeText, Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
        if (nodeText == null) {
            throw new NullPointerException();
        }
        CsmElement element = ConcreteSyntaxModel.forClass(observedNode.getClass());
        CalculatedSyntaxModel original = calculatedSyntaxModelForNode(element, observedNode);
        CalculatedSyntaxModel after = calculatedSyntaxModelAfterPropertyChange(element, observedNode, property, oldValue, newValue);
        Difference difference = Difference.calculate(original, after);
        //System.out.println("DIFFERENCE " + difference);
        difference.apply(nodeText);
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

    public static boolean isWhitespace(int tokenType) {
        return tokenType == 0 || tokenType == 3 || tokenType == 1 || tokenType == 32 || tokenType == 31;
    }

    public static boolean isWhitespace(CsmElement csmElement) {
        return csmElement instanceof CsmToken && isWhitespace(((CsmToken)csmElement).getTokenType());
    }

    private void calculatedSyntaxModelForNode(CsmElement csm, Node node, List<CsmElement> elements, Change change) {
        if (csm instanceof CsmSequence) {
            CsmSequence csmSequence = (CsmSequence) csm;
            csmSequence.getElements().forEach(e -> calculatedSyntaxModelForNode(e, node, elements, change));
        } else if (csm instanceof CsmComment) {
//            Object valueRaw = change.getValue(ObservableProperty.COMMENT, node);
//            if (valueRaw instanceof Optional) {
//                if (((Optional)valueRaw).isPresent()) {
//                    valueRaw = ((Optional)valueRaw).get();
//                } else {
//                    valueRaw = null;
//                }
//            }
//            if (valueRaw != null) {
//                Comment comment = (Comment) valueRaw;
//                if (comment instanceof JavadocComment) {
//                    elements.add(new CsmToken(ASTParserConstants.JAVA_DOC_COMMENT, "/**" + ((JavadocComment)comment).getContent() + "*/"));
//                    elements.add(new CsmToken(3));
//                } else {
//                    throw new UnsupportedOperationException(valueRaw.getClass().getSimpleName());
//                }
//            }
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
                        //findCompulsoryTokens(it.next());
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
            // nothing to do
        } else if (csm instanceof CsmUnindent) {
            // nothing to do
        } else if (csm instanceof CsmAttribute) {
            CsmAttribute csmAttribute = (CsmAttribute)csm;
            Object value = change.getValue(csmAttribute.getProperty(), node);
            throw new UnsupportedOperationException((String)value);
        } else {
            throw new UnsupportedOperationException(csm.getClass().getSimpleName());
        }
    }

    private int toToken(Modifier modifier) {
        switch (modifier) {
            case PUBLIC:
                return ASTParserConstants.PUBLIC;
            case PRIVATE:
                return ASTParserConstants.PRIVATE;
            case PROTECTED:
                return ASTParserConstants.PROTECTED;
            case STATIC:
                return ASTParserConstants.STATIC;
            default:
                throw new UnsupportedOperationException(modifier.name());
        }
    }

    CalculatedSyntaxModel calculatedSyntaxModelAfterPropertyChange(Node node, ObservableProperty property, Object oldValue, Object newValue) {
        return calculatedSyntaxModelAfterPropertyChange(ConcreteSyntaxModel.forClass(node.getClass()), node, property, oldValue, newValue);
    }

    // Visible for testing
    CalculatedSyntaxModel calculatedSyntaxModelAfterPropertyChange(CsmElement csm, Node node, ObservableProperty property, Object oldValue, Object newValue) {
        List<CsmElement> elements = new LinkedList<CsmElement>();
        calculatedSyntaxModelForNode(csm, node, elements, new PropertyChange(property, oldValue, newValue));
        return new CalculatedSyntaxModel(elements);
    }

}
