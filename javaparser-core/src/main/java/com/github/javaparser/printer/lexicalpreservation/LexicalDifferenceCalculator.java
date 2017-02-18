package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.concretesyntaxmodel.*;

import javax.xml.soap.Text;
import java.util.*;

public class LexicalDifferenceCalculator {

    class CalculatedSyntaxModel {
        List<CsmElement> elements;

        public CalculatedSyntaxModel(List<CsmElement> elements) {
            this.elements = elements;
        }

        public CalculatedSyntaxModel from(int index) {
            return new CalculatedSyntaxModel(elements.subList(index, elements.size()));
        }

        @Override
        public String toString() {
            return "CalculatedSyntaxModel{" +
                    "elements=" + elements +
                    '}';
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

    class CsmChild implements CsmElement {
        private Node child;

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

    interface Change {

    }

    class NoChange implements Change {

    }

    class PropertyChange implements Change {
        private ObservableProperty property;
        private Object oldValue;
        private Object newValue;

        public PropertyChange(ObservableProperty property, Object oldValue, Object newValue) {
            this.property = property;
            this.oldValue = oldValue;
            this.newValue = newValue;
        }
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
            if (change instanceof PropertyChange && ((PropertyChange)change).property == csmSingleReference.getProperty()) {
                child = (Node)((PropertyChange)change).newValue;
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
                        }
                        if (true) throw new UnsupportedOperationException(it.next().toString());
                        //findCompulsoryTokens(it.next());
                        if (it.hasNext()) {
                            calculatedSyntaxModelFor(csmList.getSeparatorPost(), node, elements, change);
                        }
                        first = false;
                    }
                    calculatedSyntaxModelFor(csmList.getFollowing(), node, elements, change);
                }
            }
        } else {
            throw new UnsupportedOperationException(csm.getClass().getSimpleName());
        }
    }

    private CalculatedSyntaxModel calculatedSyntaxModelAfterPropertyChange(CsmElement csm, Node node, ObservableProperty property, Object oldValue, Object newValue) {
        List<CsmElement> elements = new LinkedList<CsmElement>();
        calculatedSyntaxModelFor(csm, node, elements, new PropertyChange(property, oldValue, newValue));
        return new CalculatedSyntaxModel(elements);
    }

    private int calculatePropertyChange(NodeText nodeText, int index, CsmElement element, Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
        if (element instanceof CsmSequence) {
            CsmSequence csmSequence = (CsmSequence) element;
            for (CsmElement child : csmSequence.getElements()) {
                index = calculatePropertyChange(nodeText, index, child, observedNode, property, oldValue, newValue);
            }
            return index;
        } else if (element instanceof CsmSingleReference) {
            CsmSingleReference csmSingleReference = (CsmSingleReference)element;
            if (csmSingleReference.getProperty() == property) {
                if (oldValue == null) {
//                    TextElement textElement = nodeText.getElements().get(index);
//                    if (!(textElement instanceof ChildTextElement)) {
//                        throw new IllegalStateException();
//                    }
//                    if (oldValue != ((ChildTextElement) textElement).getChild()) {
//                        throw new IllegalStateException();
//                    }
                    return index;
                } else {
                    throw new UnsupportedOperationException();
                }
            } else {
                return index + 1;
            }
        } else if (element instanceof CsmComment) {
            return index;
        } else if (element instanceof CsmList) {
            CsmList csmList = (CsmList)element;
            return index;
        } else {
            throw new UnsupportedOperationException(element.getClass().getSimpleName());
        }
    }

    /**
     * A Difference should give me a sequence of elements I should find (to indicate the context) followed by a list of elements
     * to remove or to add and follow by another sequence of elements.
     *
     * I should later be able to apply such difference to a nodeText.
     */
    public static class Difference {

        private List<DifferenceElement> elements;

        private Difference(List<DifferenceElement> elements) {
            this.elements = elements;
        }

        private interface DifferenceElement {

        }

        private static class Added implements DifferenceElement {
            CsmElement element;

            public Added(CsmElement element) {
                this.element = element;
            }

            @Override
            public String toString() {
                return "Added{" + element + '}';
            }
        }

        private static class Kept implements DifferenceElement  {
            CsmElement element;

            public Kept(CsmElement element) {
                this.element = element;
            }

            @Override
            public String toString() {
                return "Kept{" + element + '}';
            }
        }

        private static class Removed implements DifferenceElement  {
            CsmElement element;

            public Removed(CsmElement element) {
                this.element = element;
            }

            @Override
            public String toString() {
                return "Removed{" + element + '}';
            }
        }

        private static boolean matching(CsmElement a, CsmElement b) {
            if (a instanceof CsmChild) {
                if (b instanceof CsmChild) {
                    CsmChild childA = (CsmChild) a;
                    CsmChild childB = (CsmChild) b;
                    return childA.child.equals(childB.child);
                } else if (b instanceof CsmToken) {
                    return false;
                } else {
                    throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
                }
            } else if (a instanceof CsmToken) {
                if (b instanceof CsmToken) {
                    CsmToken childA = (CsmToken)a;
                    CsmToken childB = (CsmToken)b;
                    return childA.getTokenType() == childB.getTokenType();
                } else if (b instanceof CsmChild) {
                    return false;
                }
            }
            throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
        }

        public static Difference calculate(CalculatedSyntaxModel original, CalculatedSyntaxModel after) {
            List<DifferenceElement> elements = new LinkedList<>();

            int originalIndex = 0;
            int afterIndex = 0;

            do {
                if (originalIndex < original.elements.size() && afterIndex >= after.elements.size()) {
                    elements.add(new Removed(original.elements.get(originalIndex)));
                    originalIndex++;
                } else if (originalIndex >= original.elements.size() && afterIndex < after.elements.size()) {
                    elements.add(new Added(after.elements.get(originalIndex)));
                    afterIndex++;
                } else {
                    CsmElement nextOriginal = original.elements.get(originalIndex);
                    CsmElement nextAfter = after.elements.get(afterIndex);
                    if (matching(nextOriginal, nextAfter)) {
                        elements.add(new Kept(nextOriginal));
                        originalIndex++;
                        afterIndex++;
                    } else {
                        //System.out.println("NOT MATCHING " + original.elements.get(originalIndex) + " " + after.elements.get(afterIndex));
                        // We can try to remove the element or add it and look which one leads to the lower difference
                        Difference removing = calculate(original.from(originalIndex + 1), after);
                        Difference adding = calculate(original, after.from(afterIndex + 1));
                        if (removing.cost() >= adding.cost()) {
                            elements.add(new Added(nextAfter));
                            afterIndex++;
                        } else {
                            elements.add(new Removed(nextOriginal));
                            originalIndex++;
                        }
                        //throw new UnsupportedOperationException("B");
                    }
                }
            } while (originalIndex < original.elements.size() || afterIndex < after.elements.size());

            //System.out.println("ORIGINAL " + original);
            //System.out.println("AFTER " + after);
            return new Difference(elements);
        }

        private TextElement toTextElement(LexicalPreservingPrinter lpp, CsmElement csmElement) {
            if (csmElement instanceof CsmChild) {
                return new ChildTextElement(lpp, ((CsmChild)csmElement).child);
            } else {
                throw new UnsupportedOperationException(csmElement.getClass().getSimpleName());
            }
        }

        private boolean isWhitespace(int tokenType) {
            return tokenType == 3 || tokenType == 1;
        }

        public void apply(NodeText nodeText) {
            int diffIndex = 0;
            int nodeTextIndex = 0;
            boolean comingFromRemoved = false;
            do {
                if (diffIndex < this.elements.size() && nodeTextIndex >= nodeText.getElements().size()) {
                    DifferenceElement diffEl = elements.get(diffIndex);
                    if (diffEl instanceof Kept) {
                        Kept kept = (Kept)diffEl;
                        if (kept.element instanceof CsmToken) {
                            CsmToken csmToken = (CsmToken)kept.element;
                            if (isWhitespace(csmToken.getTokenType())) {
                                diffIndex++;
                            } else {
                                throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: " + nodeText + ". Difference: " + this);
                            }
                        } else {
                            throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: " + nodeText + ". Difference: " + this);
                        }
                        comingFromRemoved = false;
                    } else {
                        throw new UnsupportedOperationException(diffEl.getClass().getSimpleName());
                    }
                } else if (diffIndex >= this.elements.size() && nodeTextIndex < nodeText.getElements().size()) {
                    TextElement nodeTextEl = nodeText.getElements().get(nodeTextIndex);
                    if ((nodeTextEl instanceof TokenTextElement) && ((TokenTextElement)nodeTextEl).isWhiteSpace()) {
                        nodeTextIndex++;
                    } else {
                        throw new UnsupportedOperationException("B " + nodeText + ". Difference: " + this + " " + nodeTextEl);
                    }
                } else {
                    DifferenceElement diffEl = elements.get(diffIndex);
                    TextElement nodeTextEl = nodeText.getElements().get(nodeTextIndex);
                    if (diffEl instanceof Added) {
                        nodeText.addElement(nodeTextIndex, toTextElement(nodeText.getLexicalPreservingPrinter(), ((Added) diffEl).element));
                        diffIndex++;
                        nodeTextIndex++;
                        comingFromRemoved = false;
                    } else if (diffEl instanceof Kept) {
                        Kept kept = (Kept)diffEl;
                        if ((kept.element instanceof CsmChild) && nodeTextEl instanceof ChildTextElement) {
                            diffIndex++;
                            nodeTextIndex++;
                        } else if ((kept.element instanceof CsmChild) && nodeTextEl instanceof TokenTextElement) {
                            if (((TokenTextElement) nodeTextEl).isWhiteSpace()) {
                                if (comingFromRemoved) {
                                    nodeText.removeElement(nodeTextIndex);
                                } else {
                                    nodeTextIndex++;
                                }
                            } else {
                                throw new UnsupportedOperationException("kept " + kept.element + " vs " + nodeTextEl);
                            }
                        } else if ((kept.element instanceof CsmToken) && nodeTextEl instanceof TokenTextElement) {
                            CsmToken csmToken = (CsmToken)kept.element;
                            TokenTextElement nodeTextToken = (TokenTextElement)nodeTextEl;
                            if (csmToken.getTokenType() == nodeTextToken.getTokenKind()) {
                                nodeTextIndex++;
                                diffIndex++;
                            } else {
                                throw new UnsupportedOperationException();
                            }
                        } else {
                            throw new UnsupportedOperationException("kept " + kept.element + " vs " + nodeTextEl);
                        }
                        comingFromRemoved = false;
                    } else if (diffEl instanceof Removed) {
                        Removed removed = (Removed)diffEl;
                        if ((removed.element instanceof CsmChild) && nodeTextEl instanceof ChildTextElement) {
                            nodeText.removeElement(nodeTextIndex);
                            diffIndex++;
                        } else {
                            throw new UnsupportedOperationException("removed " + removed.element + " vs " + nodeTextEl);
                        }
                        comingFromRemoved = true;
                    } else {
                        throw new UnsupportedOperationException("" + diffEl + " vs " + nodeTextEl);
                    }
                }
            } while (diffIndex < this.elements.size() || nodeTextIndex < nodeText.getElements().size());
        }

        public long cost() {
            return elements.stream().filter(e -> !(e instanceof Kept)).count();
        }

        @Override
        public String toString() {
            return "Difference{" + elements + '}';
        }
    }

    interface CompulsoryElement {

    }

    class ChildElement implements CompulsoryElement {
        public Node child;

        public ChildElement(Node child) {
            this.child = child;
        }

        @Override
        public String toString() {
            return "child(" + child.getClass().getSimpleName() + ")";
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            ChildElement that = (ChildElement) o;

            return child.equals(that.child);
        }

        @Override
        public int hashCode() {
            return child.hashCode();
        }
    }

    class TokenElement implements CompulsoryElement {
        int tokenType;

        public TokenElement(int tokenType) {
            this.tokenType = tokenType;
        }

        @Override
        public String toString() {
            return ASTParserConstants.tokenImage[tokenType];
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            TokenElement that = (TokenElement) o;

            return tokenType == that.tokenType;
        }

        @Override
        public int hashCode() {
            return tokenType;
        }
    }

    private List<CompulsoryElement> findCompulsoryTokens(Node node) {
        CsmElement csmElement = ConcreteSyntaxModel.forClass(node.getClass());
        return findCompulsoryTokens(csmElement, node);
    }

    private List<CompulsoryElement> findCompulsoryTokens(CsmElement csmElement, Node node) {
        if (csmElement instanceof CsmSequence) {
            CsmSequence csmSequence = (CsmSequence) csmElement;
            List<CompulsoryElement> elements = new LinkedList<>();
            csmSequence.getElements().forEach(e -> elements.addAll(findCompulsoryTokens(e, node)));
            return elements;
        } else if (csmElement instanceof CsmNone) {
            // nothing to do
            return Collections.emptyList();
        } else if (csmElement instanceof CsmComment) {
            // nothing to do
            return Collections.emptyList();
        } else if (csmElement instanceof CsmList) {
            List<CompulsoryElement> elements = new LinkedList<>();
            CsmList csmList = (CsmList) csmElement;
            if (csmList.getProperty().isAboutNodes()) {
                NodeList nodeList = csmList.getProperty().listValueFor(node);
                if (!nodeList.isEmpty()) {
                    elements.addAll(findCompulsoryTokens(csmList.getPreceeding(), node));
                    for (int i = 0; i < nodeList.size(); i++) {
                        if (i != 0) {
                            elements.addAll(findCompulsoryTokens(((CsmList) csmElement).getSeparatorPre(), node));
                        }
                        elements.add(new ChildElement(nodeList.get(i)));
                        if (i != (nodeList.size() - 1)) {
                            elements.addAll(findCompulsoryTokens(((CsmList) csmElement).getSeparatorPost(), node));
                        }

                    }
                    elements.addAll(findCompulsoryTokens(csmList.getFollowing(), node));
                }
            } else {
                Collection collection = csmList.getProperty().listPropertyFor(node);
                if (!collection.isEmpty()) {
                    elements.addAll(findCompulsoryTokens(csmList.getPreceeding(), node));

                    boolean first = true;
                    for (Iterator it = collection.iterator(); it.hasNext(); ) {
                        if (!first) {
                            elements.addAll(findCompulsoryTokens(((CsmList) csmElement).getSeparatorPre(), node));
                        }
                        if (true) throw new UnsupportedOperationException(it.next().toString());
                        //findCompulsoryTokens(it.next());
                        if (it.hasNext()) {
                            elements.addAll(findCompulsoryTokens(((CsmList) csmElement).getSeparatorPost(), node));
                        }
                        first = false;
                    }
                    elements.addAll(findCompulsoryTokens(csmList.getFollowing(), node));
                }
            }
            return elements;
        } else if (csmElement instanceof CsmToken) {
            CsmToken csmToken = (CsmToken) csmElement;
            if (csmToken.getTokenType() <= 5) {
                return Collections.emptyList();
            }
            if (csmToken.getTokenType() >= 31 && csmToken.getTokenType() <= 36) {
                return Collections.emptyList();
            }
            List<CompulsoryElement> res = new LinkedList<>();
            res.add(new TokenElement(csmToken.getTokenType()));
            return res;
        } else if (csmElement instanceof CsmConditional) {
            CsmConditional csmConditional = (CsmConditional) csmElement;
            boolean condition;
            switch (csmConditional.getCondition()) {
                case FLAG:
                    condition = (Boolean) csmConditional.getProperty().singleValueFor(node);
                    break;
                case IS_PRESENT:
                    condition = !csmConditional.getProperty().isNull(node);
                    break;
                default:
                    throw new UnsupportedOperationException(csmConditional.getCondition().toString());
            }
            if (condition) {
                return findCompulsoryTokens(csmConditional.getThenElement(), node);
            } else {
                return findCompulsoryTokens(csmConditional.getElseElement(), node);
            }
        } else if (csmElement instanceof CsmSingleReference) {
            CsmSingleReference singleReference = (CsmSingleReference) csmElement;
            List<CompulsoryElement> res = new LinkedList<>();
            res.add(new ChildElement(singleReference.getProperty().singlePropertyFor(node)));
            return res;
        } else if (csmElement instanceof CsmAttribute) {
            CsmAttribute csmAttribute = (CsmAttribute) csmElement;
            String text = csmAttribute.getProperty().singleValueFor(node).toString();
            List<CompulsoryElement> res = new LinkedList<>();
            res.add(new TokenElement(csmAttribute.getTokenType(text)));
            return res;
        } else if (csmElement instanceof CsmIndent) {
            return Collections.emptyList();
        } else if (csmElement instanceof CsmUnindent) {
            return Collections.emptyList();
        } else if (csmElement instanceof CsmOrphanCommentsEnding) {
            return Collections.emptyList();
        } else {
            throw new UnsupportedOperationException(csmElement.getClass().getSimpleName());
        }
    }
}
