package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * A Difference should give me a sequence of elements I should find (to indicate the context) followed by a list of elements
 * to remove or to add and follow by another sequence of elements.
 *
 * I should later be able to apply such difference to a nodeText.
 */
public class Difference {

    private List<DifferenceElement> elements;

    private Difference(List<DifferenceElement> elements) {
        this.elements = elements;
    }

    interface DifferenceElement {
        static DifferenceElement added(CsmElement element) {
            return new Added(element);
        }

        static DifferenceElement removed(CsmElement element) {
            return new Removed(element);
        }

        static DifferenceElement kept(CsmElement element) {
            return new Kept(element);
        }
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

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Added added = (Added) o;

            return element.equals(added.element);
        }

        @Override
        public int hashCode() {
            return element.hashCode();
        }
    }

    private static class Kept implements DifferenceElement {
        CsmElement element;

        public Kept(CsmElement element) {
            this.element = element;
        }

        @Override
        public String toString() {
            return "Kept{" + element + '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Kept kept = (Kept) o;

            return element.equals(kept.element);
        }

        @Override
        public int hashCode() {
            return element.hashCode();
        }
    }

    private static class Removed implements DifferenceElement {
        CsmElement element;

        public Removed(CsmElement element) {
            this.element = element;
        }

        @Override
        public String toString() {
            return "Removed{" + element + '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Removed removed = (Removed) o;

            return element.equals(removed.element);
        }

        @Override
        public int hashCode() {
            return element.hashCode();
        }
    }

    private static boolean matching(CsmElement a, CsmElement b) {
        if (a instanceof LexicalDifferenceCalculator.CsmChild) {
            if (b instanceof LexicalDifferenceCalculator.CsmChild) {
                LexicalDifferenceCalculator.CsmChild childA = (LexicalDifferenceCalculator.CsmChild) a;
                LexicalDifferenceCalculator.CsmChild childB = (LexicalDifferenceCalculator.CsmChild) b;
                return childA.getChild().equals(childB.getChild());
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
            } else if (b instanceof LexicalDifferenceCalculator.CsmChild) {
                return false;
            }
        } else if (a instanceof CsmIndent) {
            return b instanceof CsmIndent;
        }
        throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
    }

    private static boolean replacement(CsmElement a, CsmElement b) {
        if (a instanceof LexicalDifferenceCalculator.CsmChild) {
            if (b instanceof LexicalDifferenceCalculator.CsmChild) {
                LexicalDifferenceCalculator.CsmChild childA = (LexicalDifferenceCalculator.CsmChild) a;
                LexicalDifferenceCalculator.CsmChild childB = (LexicalDifferenceCalculator.CsmChild) b;
                return childA.getChild().getClass().equals(childB.getClass());
            } else if (b instanceof CsmToken) {
                return false;
                //throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
            } else {
                throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
            }
        } else if (a instanceof CsmToken) {
            if (b instanceof CsmToken) {
                CsmToken childA = (CsmToken)a;
                CsmToken childB = (CsmToken)b;
                //throw new UnsupportedOperationException(childA + " "+childB);
                return childA.getTokenType() == childB.getTokenType();
            } else if (b instanceof LexicalDifferenceCalculator.CsmChild) {
                //throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
                return false;
            }
        }
        throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
    }

    private static Map<Node, Integer> findChildrenPositions(LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel) {
        Map<Node, Integer> positions = new HashMap<>();
        for (int i=0;i<calculatedSyntaxModel.elements.size();i++) {
            CsmElement element = calculatedSyntaxModel.elements.get(i);
            if (element instanceof LexicalDifferenceCalculator.CsmChild) {
                positions.put(((LexicalDifferenceCalculator.CsmChild)element).getChild(), i);
            }
        }
        return positions;
    }

    public static Difference calculate(LexicalDifferenceCalculator.CalculatedSyntaxModel original, LexicalDifferenceCalculator.CalculatedSyntaxModel after) {
        //Prima potrei trovare i punti fissi guardando i child e i token non di white space.
        //A quel punto le differenze le calcolerei solo su quello che rimane

        Map<Node, Integer> childrenInOriginal = findChildrenPositions(original);
        Map<Node, Integer> childrenInAfter = findChildrenPositions(after);

        List<Node> commonChildren = new LinkedList<>(childrenInOriginal.keySet());
        commonChildren.retainAll(childrenInAfter.keySet());
        commonChildren.sort((a, b) -> Integer.compare(childrenInOriginal.get(a), childrenInOriginal.get(b)));

        List<DifferenceElement> elements = new LinkedList<>();

        int originalIndex = 0;
        int afterIndex = 0;
        int commonChildrenIndex = 0;
        while (commonChildrenIndex < commonChildren.size()) {
            Node child = commonChildren.get(commonChildrenIndex++);
            int posOfNextChildInOriginal = childrenInOriginal.get(child);
            int posOfNextChildInAfter    = childrenInAfter.get(child);
            if (originalIndex < posOfNextChildInOriginal || afterIndex < posOfNextChildInAfter) {
                elements.addAll(calculateImpl(original.sub(originalIndex, posOfNextChildInOriginal), after.sub(afterIndex, posOfNextChildInAfter)).elements);
            }
            elements.add(new Kept(new LexicalDifferenceCalculator.CsmChild(child)));
            originalIndex = posOfNextChildInOriginal + 1;
            afterIndex = posOfNextChildInAfter + 1;
        }

        if (originalIndex < original.elements.size() || afterIndex < after.elements.size()) {
            elements.addAll(calculateImpl(original.sub(originalIndex, original.elements.size()), after.sub(afterIndex, after.elements.size())).elements);
        }
        return new Difference(elements);
    }

    private static Difference calculateImpl(LexicalDifferenceCalculator.CalculatedSyntaxModel original, LexicalDifferenceCalculator.CalculatedSyntaxModel after) {
        List<DifferenceElement> elements = new LinkedList<>();

        int originalIndex = 0;
        int afterIndex = 0;
        boolean comingFromAdded = false;

        do {
            if (originalIndex < original.elements.size() && afterIndex >= after.elements.size()) {
                elements.add(new Removed(original.elements.get(originalIndex)));
                originalIndex++;
                comingFromAdded = false;
            } else if (originalIndex >= original.elements.size() && afterIndex < after.elements.size()) {
                elements.add(new Added(after.elements.get(afterIndex)));
                afterIndex++;
                comingFromAdded = true;
            } else {
                CsmElement nextOriginal = original.elements.get(originalIndex);
                CsmElement nextAfter = after.elements.get(afterIndex);
                if (matching(nextOriginal, nextAfter)) {
                    elements.add(new Kept(nextOriginal));
                    comingFromAdded = false;
                    originalIndex++;
                    afterIndex++;
                } else if (replacement(nextOriginal, nextAfter)) {
                    elements.add(new Removed(nextOriginal));
                    elements.add(new Added(nextAfter));
                    comingFromAdded = false;
                    originalIndex++;
                    afterIndex++;
                //} else if (LexicalDifferenceCalculator.isWhitespaceOrComment(nextOriginal)) {
                //    originalIndex++;
//                } else if (LexicalDifferenceCalculator.isWhitespaceOrComment(nextAfter)) {
//                    if (comingFromAdded) {
//                        elements.add(new Added(nextAfter));
//                    }
//                    afterIndex++;
                } else {
                    //System.out.println("NOT MATCHING " + original.elements.get(originalIndex) + " " + after.elements.get(afterIndex));
                    // We can try to remove the element or add it and look which one leads to the lower difference
                    Difference adding = calculate(original.from(originalIndex), after.from(afterIndex + 1));
                    Difference removing = null;
                    if (adding.cost() > 0) {
                        removing = calculate(original.from(originalIndex + 1), after.from(afterIndex));
                    }

                    if (removing == null || removing.cost() > adding.cost()) {
                        elements.add(new Added(nextAfter));
                        comingFromAdded = true;
                        afterIndex++;
                    } else {
                        elements.add(new Removed(nextOriginal));
                        comingFromAdded = false;
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
        if (csmElement instanceof LexicalDifferenceCalculator.CsmChild) {
            return new ChildTextElement(lpp, ((LexicalDifferenceCalculator.CsmChild) csmElement).getChild());
        } else if (csmElement instanceof CsmToken) {
            return new TokenTextElement(((CsmToken) csmElement).getTokenType(), ((CsmToken) csmElement).getContent(null));
        } else {
            throw new UnsupportedOperationException(csmElement.getClass().getSimpleName());
        }
    }

    private List<TextElement> processIndentation(List<TokenTextElement> indentation, List<TextElement> prevElements) {
        List<TextElement> res = new LinkedList<>();
        res.addAll(indentation);
        boolean afterNl = false;
        for (TextElement e : prevElements) {
            if (e.isToken(3) || e.isToken(31)) {
                res.clear();
                afterNl = true;
            } else {
                if (afterNl && e instanceof TokenTextElement && LexicalDifferenceCalculator.isWhitespace(((TokenTextElement)e).getTokenKind())) {
                    res.add(e);
                } else {
                    afterNl = false;
                }
            }
        }
        return res;
    }

    private List<TextElement> indentationBlock() {
        List<TextElement> res = new LinkedList<>();
        res.add(new TokenTextElement(1));
        res.add(new TokenTextElement(1));
        res.add(new TokenTextElement(1));
        res.add(new TokenTextElement(1));
        return res;
    }

    private int considerCleaningTheLine(NodeText nodeText, int nodeTextIndex) {
        while (nodeTextIndex >=1 && nodeText.getElements().get(nodeTextIndex - 1).isWhiteSpace() && !nodeText.getElements().get(nodeTextIndex - 1).isToken(3)) {
            nodeText.removeElement(nodeTextIndex - 1);
            nodeTextIndex--;
        }
        return nodeTextIndex;
    }

    public void apply(NodeText nodeText, Node node) {
        List<TokenTextElement> indentation = nodeText.getLexicalPreservingPrinter().findIndentation(node);
        if (nodeText == null) {
            throw new NullPointerException();
        }
        int diffIndex = 0;
        int nodeTextIndex = 0;
        boolean comingFromRemoved = false;
        boolean comingFromAdded = false;
        do {
            if (diffIndex < this.elements.size() && nodeTextIndex >= nodeText.getElements().size()) {
                DifferenceElement diffEl = elements.get(diffIndex);
                if (diffEl instanceof Kept) {
                    Kept kept = (Kept) diffEl;
                    if (kept.element instanceof CsmToken) {
                        CsmToken csmToken = (CsmToken) kept.element;
                        if (LexicalDifferenceCalculator.isWhitespaceOrComment(csmToken.getTokenType())) {
                            diffIndex++;
                        } else {
                            throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: " + nodeText + ". Difference: " + this);
                        }
                    } else {
                        throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: " + nodeText + ". Difference: " + this);
                    }
                    comingFromRemoved = false;
                    comingFromAdded = false;
                } else if (diffEl instanceof Added) {
                    nodeText.addElement(nodeTextIndex, toTextElement(nodeText.getLexicalPreservingPrinter(), ((Added) diffEl).element));
                    nodeTextIndex++;
                    diffIndex++;
                } else {
                    throw new UnsupportedOperationException(diffEl.getClass().getSimpleName());
                }
            } else if (diffIndex >= this.elements.size() && nodeTextIndex < nodeText.getElements().size()) {
                TextElement nodeTextEl = nodeText.getElements().get(nodeTextIndex);
                if ((nodeTextEl instanceof TokenTextElement) && ((TokenTextElement)nodeTextEl).isWhiteSpaceOrComment()) {
                    nodeTextIndex++;
                } else {
                    throw new UnsupportedOperationException("B " + nodeText + ". Difference: " + this + " " + nodeTextEl);
                }
            } else {
                DifferenceElement diffEl = elements.get(diffIndex);
                TextElement nodeTextEl = nodeText.getElements().get(nodeTextIndex);
                if (diffEl instanceof Added) {
                    TextElement textElement = toTextElement(nodeText.getLexicalPreservingPrinter(), ((Added) diffEl).element);
                    boolean used = false;
                    if (nodeTextIndex > 0 && nodeText.getElements().get(nodeTextIndex - 1).isToken(3)) {
                        for (TextElement e : processIndentation(indentation, nodeText.getElements().subList(0, nodeTextIndex - 1))) {
                            nodeText.addElement(nodeTextIndex++, e);
                        }
                    } else if (nodeTextIndex > 0 && nodeText.getElements().get(nodeTextIndex - 1).isToken(ASTParserConstants.LBRACE)) {
                        if (textElement.isToken(3)) {
                            used = true;
                        }
                        nodeText.addElement(nodeTextIndex++, new TokenTextElement(3));
                        for (TextElement e : processIndentation(indentation, nodeText.getElements().subList(0, nodeTextIndex - 1))) {
                            nodeText.addElement(nodeTextIndex++, e);
                        }
                        for (TextElement e : indentationBlock()) {
                            nodeText.addElement(nodeTextIndex++, e);
                        }
                    }
                    if (!used) {
                        nodeText.addElement(nodeTextIndex, textElement);
                        nodeTextIndex++;
                    }
                    diffIndex++;
                    comingFromRemoved = false;
                    comingFromAdded = true;
                } else if (diffEl instanceof Kept) {
                    Kept kept = (Kept)diffEl;
                    if ((kept.element instanceof LexicalDifferenceCalculator.CsmChild) && nodeTextEl instanceof ChildTextElement) {
                        diffIndex++;
                        nodeTextIndex++;
                    } else if ((kept.element instanceof LexicalDifferenceCalculator.CsmChild) && nodeTextEl instanceof TokenTextElement) {
                        if (((TokenTextElement) nodeTextEl).isWhiteSpaceOrComment()) {
                            //if (comingFromRemoved) {
                                //nodeText.removeElement(nodeTextIndex);
                            //} else {
                                nodeTextIndex++;
                            //}
                        } else {
                            if (kept.element instanceof LexicalDifferenceCalculator.CsmChild) {
                                LexicalDifferenceCalculator.CsmChild keptChild = (LexicalDifferenceCalculator.CsmChild)kept.element;
                                if (keptChild.getChild() instanceof PrimitiveType) {
                                    nodeTextIndex++;
                                    diffIndex++;
                                } else {
                                    throw new UnsupportedOperationException("kept " + kept.element + " vs " + nodeTextEl);
                                }
                            } else {
                                throw new UnsupportedOperationException("kept " + kept.element + " vs " + nodeTextEl);
                            }
                        }
                    } else if ((kept.element instanceof CsmToken) && nodeTextEl instanceof TokenTextElement) {
                        CsmToken csmToken = (CsmToken) kept.element;
                        TokenTextElement nodeTextToken = (TokenTextElement) nodeTextEl;
                        if (csmToken.getTokenType() == nodeTextToken.getTokenKind()) {
                            nodeTextIndex++;
                            diffIndex++;
                        } else if (LexicalDifferenceCalculator.isWhitespaceOrComment(csmToken.getTokenType())) {
                            diffIndex++;
                        } else if (nodeTextToken.isWhiteSpaceOrComment()) {
                            nodeTextIndex++;
                        } else {
                            throw new UnsupportedOperationException("CSM TOKEN " + csmToken + " NodeText TOKEN " + nodeTextToken);
                        }
                    } else if ((kept.element instanceof CsmToken) && ((CsmToken) kept.element).isWhiteSpace()) {
                        diffIndex++;
                    } else {
                        throw new UnsupportedOperationException("kept " + kept.element + " vs " + nodeTextEl);
                    }
                    comingFromRemoved = false;
                    comingFromAdded = false;
                } else if (diffEl instanceof Removed) {
                    Removed removed = (Removed)diffEl;
                    if ((removed.element instanceof LexicalDifferenceCalculator.CsmChild) && nodeTextEl instanceof ChildTextElement) {
                        nodeText.removeElement(nodeTextIndex);
                        if (nodeTextIndex < nodeText.getElements().size() && nodeText.getElements().get(nodeTextIndex).isToken(3)) {
                            nodeTextIndex = considerCleaningTheLine(nodeText, nodeTextIndex);
                        }
                        diffIndex++;
                    } else if ((removed.element instanceof CsmToken) && nodeTextEl instanceof TokenTextElement
                            && ((CsmToken)removed.element).getTokenType() == ((TokenTextElement)nodeTextEl).getTokenKind()) {
                        nodeText.removeElement(nodeTextIndex);
                        diffIndex++;
                    } else if (nodeTextEl instanceof TokenTextElement
                            && ((TokenTextElement)nodeTextEl).isWhiteSpaceOrComment()) {
                        nodeTextIndex++;
                    } else if (removed.element instanceof CsmToken && ((CsmToken)removed.element).isWhiteSpace()) {
                        diffIndex++;
                    } else if (removed.element instanceof LexicalDifferenceCalculator.CsmChild && ((LexicalDifferenceCalculator.CsmChild)removed.element).getChild() instanceof PrimitiveType) {
                        if (isPrimitiveType(nodeTextEl)) {
                            nodeText.removeElement(nodeTextIndex);
                            diffIndex++;
                        } else {
                            throw new UnsupportedOperationException("removed " + removed.element + " vs " + nodeTextEl);
                        }
                    } else {
                        throw new UnsupportedOperationException("removed " + removed.element + " vs " + nodeTextEl);
                    }
                    comingFromRemoved = true;
                    comingFromAdded = false;
                } else {
                    throw new UnsupportedOperationException("" + diffEl + " vs " + nodeTextEl);
                }
            }
        } while (diffIndex < this.elements.size() || nodeTextIndex < nodeText.getElements().size());
    }

    private boolean isPrimitiveType(TextElement textElement) {
        if (textElement instanceof TokenTextElement) {
            TokenTextElement tokenTextElement = (TokenTextElement)textElement;
            if (tokenTextElement.getTokenKind() == ASTParserConstants.BYTE) {
                return true;
            }
            if (tokenTextElement.getTokenKind() == ASTParserConstants.CHAR) {
                return true;
            }
            if (tokenTextElement.getTokenKind() == ASTParserConstants.SHORT) {
                return true;
            }
            if (tokenTextElement.getTokenKind() == ASTParserConstants.INT) {
                return true;
            }
            if (tokenTextElement.getTokenKind() == ASTParserConstants.LONG) {
                return true;
            }
            if (tokenTextElement.getTokenKind() == ASTParserConstants.FLOAT) {
                return true;
            }
            if (tokenTextElement.getTokenKind() == ASTParserConstants.DOUBLE) {
                return true;
            }
            return false;
        } else {
            return false;
        }
    }

    public long cost() {
        return elements.stream().filter(e -> !(e instanceof Kept)).count();
    }

    @Override
    public String toString() {
        return "Difference{" + elements + '}';
    }

    public List<DifferenceElement> getElements() {
        return elements;
    }
}
