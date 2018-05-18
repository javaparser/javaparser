package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;

import java.util.*;

import static com.github.javaparser.GeneratedJavaParserConstants.*;

/**
 * A Difference should give me a sequence of elements I should find (to indicate the context) followed by a list of elements
 * to remove or to add and follow by another sequence of elements.
 *
 * I should later be able to apply such difference to a nodeText.
 */
public class Difference {

    private static final int STANDARD_INDENTATION_SIZE = 4;

    private final List<DifferenceElement> elements;

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

        /**
         * Return the CsmElement considered in this DifferenceElement.
         */
        CsmElement getElement();

        boolean isAdded();
    }

    private static class Added implements DifferenceElement {
        final CsmElement element;

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

        @Override
        public CsmElement getElement() {
            return element;
        }

        @Override
        public boolean isAdded() {
            return true;
        }

        public boolean isIndent() { return element instanceof CsmIndent; }

        public boolean isUnindent() { return element instanceof CsmUnindent; }

        public TextElement toTextElement() {
            if (element instanceof CsmChild) {
                return new ChildTextElement(((CsmChild) element).getChild());
            } else if (element instanceof CsmToken) {
                return new TokenTextElement(((CsmToken) element).getTokenType(), ((CsmToken) element).getContent(null));
            } else {
                throw new UnsupportedOperationException(element.getClass().getSimpleName());
            }
        }
    }

    /**
     * Elements in a CsmMix have been reshuffled. It could also mean that
     * some new elements have been added or removed to the mix.
     */
    private static class Reshuffled implements DifferenceElement {
        final CsmMix previousOrder;
        final CsmMix element;

        public Reshuffled(CsmMix previousOrder, CsmMix element) {
            this.previousOrder = previousOrder;
            this.element = element;
        }

        @Override
        public String toString() {
            return "Reshuffled{" + element + ", previous="+ previousOrder+ '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Reshuffled that = (Reshuffled) o;

            if (!previousOrder.equals(that.previousOrder)) return false;
            return element.equals(that.element);
        }

        @Override
        public int hashCode() {
            int result = previousOrder.hashCode();
            result = 31 * result + element.hashCode();
            return result;
        }

        @Override
        public CsmMix getElement() {
            return element;
        }

        @Override
        public boolean isAdded() {
            return false;
        }
    }

    private static class Kept implements DifferenceElement {
        final CsmElement element;

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

        @Override
        public CsmElement getElement() {
            return element;
        }

        @Override
        public boolean isAdded() {
            return false;
        }

        public boolean isIndent() { return element instanceof CsmIndent; }

        public boolean isUnindent() { return element instanceof CsmUnindent; }

        public boolean isToken() { return element instanceof CsmToken; }

        public boolean isChild() { return element instanceof CsmChild; }

        public boolean isPrimitiveType() {
            if (isChild()) {
                CsmChild csmChild = (CsmChild) element;
                return csmChild.getChild() instanceof PrimitiveType;
            }

            return false;
        }

        public boolean isWhiteSpaceOrComment() {
            if (isToken()) {
                CsmToken csmToken = (CsmToken) element;
                return TokenTypes.isWhitespaceOrComment(csmToken.getTokenType());
            }

            return false;
        }
    }

    private static class Removed implements DifferenceElement {
        final CsmElement element;

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

        @Override
        public CsmElement getElement() {
            return element;
        }

        @Override
        public boolean isAdded() {
            return false;
        }

        public boolean isToken() { return element instanceof CsmToken; }

        public boolean isChild() { return element instanceof CsmChild; }

        public boolean isPrimitiveType() {
            if (isChild()) {
                CsmChild csmChild = (CsmChild) element;
                return csmChild.getChild() instanceof PrimitiveType;
            }

            return false;
        }

        public boolean isWhiteSpace() {
            if(isToken()) {
                CsmToken csmToken = (CsmToken) element;
                return csmToken.isWhiteSpace();
            }

            return false;
        }
    }

    private static boolean matching(CsmElement a, CsmElement b) {
        if (a instanceof CsmChild) {
            if (b instanceof CsmChild) {
                CsmChild childA = (CsmChild) a;
                CsmChild childB = (CsmChild) b;
                return childA.getChild().equals(childB.getChild());
            } else if (b instanceof CsmToken) {
                return false;
            } else if (b instanceof CsmIndent) {
                return false;
            } else if (b instanceof CsmUnindent) {
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
            } else if (b instanceof CsmIndent) {
                return false;
            } else if (b instanceof CsmUnindent) {
                return false;
            } else {
                throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
            }
        } else if (a instanceof CsmIndent) {
            return b instanceof CsmIndent;
        } else if (a instanceof CsmUnindent) {
            return b instanceof CsmUnindent;
        }
        throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
    }

    private static boolean replacement(CsmElement a, CsmElement b) {
        if (a instanceof CsmIndent || b instanceof CsmIndent || a instanceof CsmUnindent || b instanceof CsmUnindent) {
            return false;
        }
        if (a instanceof CsmChild) {
            if (b instanceof CsmChild) {
                CsmChild childA = (CsmChild) a;
                CsmChild childB = (CsmChild) b;
                return childA.getChild().getClass().equals(childB.getChild().getClass());
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

    /**
     * Find the positions of all the given children.
     */
    private static Map<Node, Integer> findChildrenPositions(LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel) {
        Map<Node, Integer> positions = new HashMap<>();
        for (int i=0;i<calculatedSyntaxModel.elements.size();i++) {
            CsmElement element = calculatedSyntaxModel.elements.get(i);
            if (element instanceof CsmChild) {
                positions.put(((CsmChild)element).getChild(), i);
            }
        }
        return positions;
    }

    /**
     * Calculate the Difference between two CalculatedSyntaxModel elements, determining which elements were kept,
     * which were added and which were removed.
     */
    static Difference calculate(LexicalDifferenceCalculator.CalculatedSyntaxModel original, LexicalDifferenceCalculator.CalculatedSyntaxModel after) {
        // For performance reasons we use the positions of matching children
        // to guide the calculation of the difference
        //
        // Suppose we have:
        //   qwerty[A]uiop
        //   qwer[A]uiop
        //
        // with [A] being a child and lowercase letters being tokens
        //
        // We would calculate the Difference between "qwerty" and "qwer" then we know the A is kept, and then we
        // would calculate the difference between "uiop" and "uiop"

        Map<Node, Integer> childrenInOriginal = findChildrenPositions(original);
        Map<Node, Integer> childrenInAfter = findChildrenPositions(after);

        List<Node> commonChildren = new LinkedList<>(childrenInOriginal.keySet());
        commonChildren.retainAll(childrenInAfter.keySet());
        commonChildren.sort(Comparator.comparingInt(childrenInOriginal::get));

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
            elements.add(new Kept(new CsmChild(child)));
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

        // We move through the two CalculatedSyntaxModel, moving both forward when we have a match
        // and moving just one side forward when we have an element kept or removed

        do {
            if (originalIndex < original.elements.size() && afterIndex >= after.elements.size()) {
                elements.add(new Removed(original.elements.get(originalIndex)));
                originalIndex++;
            } else if (originalIndex >= original.elements.size() && afterIndex < after.elements.size()) {
                elements.add(new Added(after.elements.get(afterIndex)));
                afterIndex++;
            } else {
                CsmElement nextOriginal = original.elements.get(originalIndex);
                CsmElement nextAfter = after.elements.get(afterIndex);

                if ((nextOriginal instanceof CsmMix) && (nextAfter instanceof CsmMix)) {
                    if (((CsmMix) nextAfter).getElements().equals(((CsmMix) nextOriginal).getElements())) {
                        // No reason to deal with a reshuffled, we are just going to keep everything as it is
                        ((CsmMix) nextAfter).getElements().forEach(el -> elements.add(new Kept(el)));
                    } else {
                        elements.add(new Reshuffled((CsmMix)nextOriginal, (CsmMix)nextAfter));
                    }
                    originalIndex++;
                    afterIndex++;
                } else if (matching(nextOriginal, nextAfter)) {
                    elements.add(new Kept(nextOriginal));
                    originalIndex++;
                    afterIndex++;
                } else if (replacement(nextOriginal, nextAfter)) {
                    elements.add(new Removed(nextOriginal));
                    elements.add(new Added(nextAfter));
                    originalIndex++;
                    afterIndex++;
                } else {
                    // We can try to remove the element or add it and look which one leads to the lower difference
                    Difference adding = calculate(original.from(originalIndex), after.from(afterIndex + 1));
                    Difference removing = null;
                    if (adding.cost() > 0) {
                        removing = calculate(original.from(originalIndex + 1), after.from(afterIndex));
                    }

                    if (removing == null || removing.cost() > adding.cost()) {
                        elements.add(new Added(nextAfter));
                        afterIndex++;
                    } else {
                        elements.add(new Removed(nextOriginal));
                        originalIndex++;
                    }
                }
            }
        } while (originalIndex < original.elements.size() || afterIndex < after.elements.size());

        return new Difference(elements);
    }

    private List<TextElement> processIndentation(List<TokenTextElement> indentation, List<TextElement> prevElements) {
        List<TextElement> res = new LinkedList<>();
        res.addAll(indentation);
        boolean afterNl = false;
        for (TextElement e : prevElements) {
            if (e.isNewline() || e.isToken(SINGLE_LINE_COMMENT)) {
                res.clear();
                afterNl = true;
            } else {
                if (afterNl && e instanceof TokenTextElement && TokenTypes.isWhitespace(((TokenTextElement)e).getTokenKind())) {
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
        res.add(new TokenTextElement(SPACE));
        res.add(new TokenTextElement(SPACE));
        res.add(new TokenTextElement(SPACE));
        res.add(new TokenTextElement(SPACE));
        return res;
    }

    private int considerCleaningTheLine(NodeText nodeText, int nodeTextIndex) {
        while (nodeTextIndex >=1 && nodeText.getElements().get(nodeTextIndex - 1).isSpaceOrTab()) {
            nodeText.removeElement(nodeTextIndex - 1);
            nodeTextIndex--;
        }
        return nodeTextIndex;
    }

    private boolean isAfterLBrace(NodeText nodeText, int nodeTextIndex) {
        if (nodeTextIndex > 0 && nodeText.getElements().get(nodeTextIndex - 1).isToken(LBRACE)) {
            return true;
        }
        if (nodeTextIndex > 0 && nodeText.getElements().get(nodeTextIndex - 1).isSpaceOrTab()) {
            return isAfterLBrace(nodeText, nodeTextIndex - 1);
        }
        return false;
    }

    /**
     * If we are at the beginning of a line, with just spaces or tabs before us we should force the space to be
     * the same as the indentation.
     */
    private int considerEnforcingIndentation(NodeText nodeText, int nodeTextIndex) {
        boolean hasOnlyWsBefore = true;
        for (int i=nodeTextIndex; i >= 0 && hasOnlyWsBefore && i < nodeText.getElements().size(); i--) {
            if (nodeText.getElements().get(i).isNewline()) {
                break;
            }
            if (!nodeText.getElements().get(i).isSpaceOrTab()) {
                hasOnlyWsBefore = false;
            }
        }
        if (hasOnlyWsBefore) {
            for (int i=nodeTextIndex; i >= 0 && i < nodeText.getElements().size(); i--) {
                if (nodeText.getElements().get(i).isNewline()) {
                    break;
                }
                nodeText.removeElement(i);
            }
        }
        return nodeTextIndex;
    }

    /**
     * Node that we have calculate the Difference we can apply to a concrete NodeText, modifying it according
     * to the difference (adding and removing the elements provided).
     */
    void apply(NodeText nodeText, Node node) {
        if (nodeText == null) {
            throw new NullPointerException();
        }
        boolean addedIndentation = false;
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(node);

        List<TextElement> givenElements = nodeText.getElements();
        int givenIndex = 0;

        List<DifferenceElement> diffElements = this.elements;
        int diffIndex = 0;
        do {
            if (diffIndex < diffElements.size() && givenIndex >= givenElements.size()) {
                DifferenceElement diffElement = diffElements.get(diffIndex);
                if (diffElement instanceof Kept) {
                    Kept kept = (Kept) diffElement;

                    if (kept.isWhiteSpaceOrComment()) {
                        diffIndex++;
                    } else {
                        throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: "
                                + nodeText + ". Difference: " + this);
                    }
                } else if (diffElement instanceof Added) {
                    Added addedElement = (Added) diffElement;

                    nodeText.addElement(givenIndex, addedElement.toTextElement());
                    givenIndex++;
                    diffIndex++;
                } else {
                    throw new UnsupportedOperationException(diffElement.getClass().getSimpleName());
                }
            } else if (diffIndex >= diffElements.size() && givenIndex < givenElements.size()) {
                TextElement givenElement = givenElements.get(givenIndex);
                if (givenElement.isWhiteSpaceOrComment()) {
                    givenIndex++;
                } else {
                    throw new UnsupportedOperationException("NodeText: " + nodeText + ". Difference: "
                            + this + " " + givenElement);
                }
            } else {
                DifferenceElement diffElement = diffElements.get(diffIndex);

                if (diffElement instanceof Added) {
                    Added addedElement = (Added) diffElement;

                    if (addedElement.isIndent()) {
                        for (int i=0;i<STANDARD_INDENTATION_SIZE;i++){
                            indentation.add(new TokenTextElement(GeneratedJavaParserConstants.SPACE));
                        }
                        addedIndentation = true;
                        diffIndex++;
                        continue;
                    }
                    if (addedElement.isUnindent()) {
                        for (int i=0;i<STANDARD_INDENTATION_SIZE && !indentation.isEmpty();i++){
                            indentation.remove(indentation.size() - 1);
                        }
                        addedIndentation = false;
                        diffIndex++;
                        continue;
                    }
                    TextElement textElement = addedElement.toTextElement();
                    boolean used = false;
                    if (givenIndex > 0 && givenElements.get(givenIndex - 1).isNewline()) {
                        for (TextElement e : processIndentation(indentation, givenElements.subList(0, givenIndex - 1))) {
                            nodeText.addElement(givenIndex++, e);
                        }
                    } else if (isAfterLBrace(nodeText, givenIndex) && !isAReplacement(diffIndex)) {
                        if (textElement.isNewline()) {
                            used = true;
                        }
                        nodeText.addElement(givenIndex++, new TokenTextElement(TokenTypes.eolTokenKind()));
                        // This remove the space in "{ }" when adding a new line
                        while (givenElements.get(givenIndex).isSpaceOrTab()) {
                            givenElements.remove(givenIndex);
                        }
                        for (TextElement e : processIndentation(indentation, givenElements.subList(0, givenIndex - 1))) {
                            nodeText.addElement(givenIndex++, e);
                        }
                        // Indentation is painful...
                        // Sometimes we want to force indentation: this is the case when indentation was expected but
                        // was actually not there. For example if we have "{ }" we would expect indentation but it is
                        // not there, so when adding new elements we force it. However if the indentation has been
                        // inserted by us in this transformation we do not want to insert it again
                        if (!addedIndentation) {
                            for (TextElement e : indentationBlock()) {
                                nodeText.addElement(givenIndex++, e);
                            }
                        }
                    }
                    if (!used) {
                        nodeText.addElement(givenIndex, textElement);
                        givenIndex++;
                    }
                    if (textElement.isNewline()) {
                        boolean followedByUnindent = (diffIndex + 1) < diffElements.size()
                                && diffElements.get(diffIndex + 1).isAdded()
                                && diffElements.get(diffIndex + 1).getElement() instanceof CsmUnindent;
                        givenIndex = adjustIndentation(indentation, nodeText, givenIndex, followedByUnindent/* && !addedIndentation*/);
                    }
                    diffIndex++;
                } else {
                    TextElement givenElement = givenElements.get(givenIndex);
                    boolean givenElementIsChild = givenElement instanceof ChildTextElement;
                    boolean givenElementIsToken = givenElement instanceof TokenTextElement;

                    if (diffElement instanceof Kept) {
                        Kept kept = (Kept)diffElement;
                        if (givenElement.isComment()) {
                            givenIndex++;
                        } else if (kept.isChild() && givenElementIsChild) {
                            diffIndex++;
                            givenIndex++;
                        } else if (kept.isChild() && givenElementIsToken) {
                            if (givenElement.isWhiteSpaceOrComment()) {
                                givenIndex++;
                            } else {
                                if (kept.isPrimitiveType()) {
                                    givenIndex++;
                                    diffIndex++;
                                } else {
                                    throw new UnsupportedOperationException("kept " + kept.element + " vs " + givenElement);
                                }
                            }
                        } else if (kept.isToken() && givenElementIsToken) {
                            CsmToken csmToken = (CsmToken) kept.element;
                            TokenTextElement nodeTextToken = (TokenTextElement) givenElement;
                            if (csmToken.getTokenType() == nodeTextToken.getTokenKind()) {
                                givenIndex++;
                                diffIndex++;
                            } else if (kept.isWhiteSpaceOrComment()) {
                                diffIndex++;
                            } else if (nodeTextToken.isWhiteSpaceOrComment()) {
                                givenIndex++;
                            } else {
                                throw new UnsupportedOperationException("Csm token " + csmToken + " NodeText TOKEN " + nodeTextToken);
                            }
                        } else if (kept.isToken() && ((CsmToken) kept.element).isWhiteSpace()) {
                            diffIndex++;
                        } else if (kept.isIndent()) {
                            // Nothing to do
                            diffIndex++;
                        } else if (kept.isUnindent()) {
                            // Nothing to do, beside considering indentation
                            diffIndex++;
                            for (int i = 0; i < STANDARD_INDENTATION_SIZE && givenIndex >= 1 && nodeText.getTextElement(givenIndex - 1).isSpaceOrTab(); i++) {
                                nodeText.removeElement(--givenIndex);
                            }
                        } else {
                            throw new UnsupportedOperationException("kept " + kept.element + " vs " + givenElement);
                        }
                    } else if (diffElement instanceof Removed) {
                        Removed removed = (Removed)diffElement;
                        if (removed.isChild() && givenElementIsChild) {
                            ChildTextElement actualChild = (ChildTextElement)givenElement;
                            if (actualChild.isComment()) {
                                CsmChild csmChild = (CsmChild)removed.element;
                                // We expected to remove a proper node but we found a comment in between.
                                // If the comment is associated to the node we want to remove we remove it as well, otherwise we keep it
                                Comment comment = (Comment)actualChild.getChild();
                                if (!comment.isOrphan() && comment.getCommentedNode().isPresent() && comment.getCommentedNode().get().equals(csmChild.getChild())) {
                                    nodeText.removeElement(givenIndex);
                                } else {
                                    givenIndex++;
                                }
                            } else {
                                nodeText.removeElement(givenIndex);
                                if (givenIndex < givenElements.size() && givenElements.get(givenIndex).isNewline()) {
                                    givenIndex = considerCleaningTheLine(nodeText, givenIndex);
                                } else {
                                    if (diffIndex + 1 >= this.getElements().size() || !(this.getElements().get(diffIndex + 1) instanceof Added)) {
                                        givenIndex = considerEnforcingIndentation(nodeText, givenIndex);
                                    }
                                    // If in front we have one space and before also we had space let's drop one space
                                    if (givenElements.size() > givenIndex && givenIndex > 0) {
                                        if (givenElements.get(givenIndex).isWhiteSpace()
                                                && givenElements.get(givenIndex - 1).isWhiteSpace()) {
                                            // However we do not want to do that when we are about to adding or removing elements
                                            if ((diffIndex + 1) == diffElements.size() || (diffElements.get(diffIndex + 1) instanceof Kept)) {
                                                givenElements.remove(givenIndex--);
                                            }
                                        }
                                    }
                                }
                                diffIndex++;
                            }
                        } else if (removed.isToken() && givenElementIsToken
                                && ((CsmToken)removed.element).getTokenType() == ((TokenTextElement)givenElement).getTokenKind()) {
                            nodeText.removeElement(givenIndex);
                            diffIndex++;
                        } else if (givenElementIsToken && givenElement.isWhiteSpaceOrComment()) {
                            givenIndex++;
                        } else if (removed.isPrimitiveType()) {
                            if (isPrimitiveType(givenElement)) {
                                nodeText.removeElement(givenIndex);
                                diffIndex++;
                            } else {
                                throw new UnsupportedOperationException("removed " + removed.element + " vs " + givenElement);
                            }
                        } else if (removed.isWhiteSpace()) {
                            diffIndex++;
                        } else if (givenElement.isWhiteSpace()) {
                            givenIndex++;
                        } else {
                            throw new UnsupportedOperationException("removed " + removed.element + " vs " + givenElement);
                        }
                    } else if (diffElement instanceof Reshuffled) {

                        // First, let's see how many tokens we need to attribute to the previous version of the of the CsmMix
                        Reshuffled reshuffled = (Reshuffled)diffElement;
                        CsmMix elementsFromPreviousOrder = reshuffled.previousOrder;
                        CsmMix elementsFromNextOrder = reshuffled.element;

                        // This contains indexes from elementsFromNextOrder to indexes from elementsFromPreviousOrder
                        Map<Integer, Integer> correspondanceBetweenNextOrderAndPreviousOrder = new HashMap<>();

                        for (int ni=0;ni<elementsFromNextOrder.getElements().size();ni++) {
                            boolean found = false;
                            CsmElement ne = elementsFromNextOrder.getElements().get(ni);
                            for (int pi=0;pi<elementsFromPreviousOrder.getElements().size() && !found;pi++) {
                                CsmElement pe = elementsFromPreviousOrder.getElements().get(pi);
                                if (!correspondanceBetweenNextOrderAndPreviousOrder.values().contains(pi)
                                        && matching(ne, pe)) {
                                    found = true;
                                    correspondanceBetweenNextOrderAndPreviousOrder.put(ni, pi);
                                }
                            }
                        }

                        // We now find out which Node Text elements corresponds to the elements in the original CSM
                        List<Integer> nodeTextIndexOfPreviousElements = findIndexOfCorrespondingNodeTextElement(elementsFromPreviousOrder.getElements(), nodeText, givenIndex, node);

                        Map<Integer, Integer> nodeTextIndexToPreviousCSMIndex = new HashMap<>();
                        for (int i=0;i<nodeTextIndexOfPreviousElements.size();i++) {
                            int value = nodeTextIndexOfPreviousElements.get(i);
                            if (value != -1) {
                                nodeTextIndexToPreviousCSMIndex.put(value, i);
                            }
                        }
                        int lastNodeTextIndex = nodeTextIndexOfPreviousElements.stream().max(Integer::compareTo).orElse(-1);

                        // Elements to be added at the end
                        List<CsmElement> elementsToBeAddedAtTheEnd = new LinkedList<>();
                        Map<Integer, List<CsmElement>> elementsToAddBeforeGivenOriginalCSMElement = new HashMap<>();
                        for (int ni=0;ni<elementsFromNextOrder.getElements().size();ni++) {
                            // If it has a mapping, then it is kept
                            if (!correspondanceBetweenNextOrderAndPreviousOrder.containsKey(ni)) {
                                // Ok, it is something new. Where to put it? Let's see what is the first following
                                // element that has a mapping
                                int originalCsmIndex = -1;
                                for (int nj=ni + 1;nj<elementsFromNextOrder.getElements().size() && originalCsmIndex==-1;nj++) {
                                    if (correspondanceBetweenNextOrderAndPreviousOrder.containsKey(nj)) {
                                        originalCsmIndex = correspondanceBetweenNextOrderAndPreviousOrder.get(nj);
                                        if (!elementsToAddBeforeGivenOriginalCSMElement.containsKey(originalCsmIndex)){
                                            elementsToAddBeforeGivenOriginalCSMElement.put(originalCsmIndex, new LinkedList<>());
                                        }
                                        elementsToAddBeforeGivenOriginalCSMElement.get(originalCsmIndex).add(elementsFromNextOrder.getElements().get(ni));
                                    }
                                }
                                // it does not preceed anything, so it goes at the end
                                if (originalCsmIndex == -1) {
                                    elementsToBeAddedAtTheEnd.add(elementsFromNextOrder.getElements().get(ni));
                                }
                            }
                        }

                        // We go over the original node text elements, in the order they appear in the NodeText.
                        // Considering an original node text element (ONE)
                        // * we verify if it corresponds to a CSM element. If it does not we just move on, otherwise
                        //   we find the correspond OCE (Original CSM Element)
                        // * we first add new elements that are marked to be added before OCE
                        // * if OCE is marked to be present also in the "after" CSM we add a kept element,
                        //   otherwise we add a removed element

                        this.getElements().remove(diffIndex);
                        int diffElIterator = diffIndex;
                        if (lastNodeTextIndex != -1) {
                            for (int ntIndex = givenIndex; ntIndex<=lastNodeTextIndex; ntIndex++) {

                                if (nodeTextIndexToPreviousCSMIndex.containsKey(ntIndex)) {
                                    int indexOfOriginalCSMElement = nodeTextIndexToPreviousCSMIndex.get(ntIndex);
                                    if (elementsToAddBeforeGivenOriginalCSMElement.containsKey(indexOfOriginalCSMElement)) {
                                        for (CsmElement elementToAdd : elementsToAddBeforeGivenOriginalCSMElement.get(indexOfOriginalCSMElement)) {
                                            diffElements.add(diffElIterator++, new Added(elementToAdd));
                                        }
                                    }

                                    CsmElement originalCSMElement = elementsFromPreviousOrder.getElements().get(indexOfOriginalCSMElement);
                                    boolean toBeKept = correspondanceBetweenNextOrderAndPreviousOrder.containsValue(indexOfOriginalCSMElement);
                                    if (toBeKept) {
                                        diffElements.add(diffElIterator++, new Kept(originalCSMElement));
                                    } else {
                                        diffElements.add(diffElIterator++, new Removed(originalCSMElement));
                                    }
                                }
                                // else we have a simple node text element, without associated csm element, just keep ignore it
                            }
                        }

                        // Finally we look for the remaining new elements that were not yet added and
                        // add all of them
                        for (CsmElement elementToAdd : elementsToBeAddedAtTheEnd) {
                            diffElements.add(diffElIterator++, new Added(elementToAdd));
                        }
                    } else {
                        throw new UnsupportedOperationException("" + diffElement + " vs " + givenElement);
                    }
                }
            }
        } while (diffIndex < diffElements.size() || givenIndex < givenElements.size());
    }

    private List<Integer> findIndexOfCorrespondingNodeTextElement(List<CsmElement> elements, NodeText nodeText, int startIndex, Node node) {
        List<Integer> correspondingIndices = new ArrayList<>();
        for (ListIterator<CsmElement> csmElementListIterator = elements.listIterator(); csmElementListIterator.hasNext(); ) {

            int previousCsmElementIndex = csmElementListIterator.previousIndex();
            CsmElement csmElement = csmElementListIterator.next();
            int nextCsmElementIndex = csmElementListIterator.nextIndex();

            Map<MatchClassification, Integer> potentialMatches = new EnumMap(MatchClassification.class);
            for (int i = startIndex; i<nodeText.getElements().size(); i++){
                if (!correspondingIndices.contains(i)) {
                    TextElement textElement = nodeText.getTextElement(i);

                    boolean isCorresponding = isCorrespondingElement(textElement, csmElement, node);

                    if (isCorresponding) {
                        boolean hasSamePreviousElement = false;
                        if (i > 0 && previousCsmElementIndex > -1) {
                            TextElement previousTextElement = nodeText.getTextElement(i - 1);

                            hasSamePreviousElement = isCorrespondingElement(previousTextElement, elements.get(previousCsmElementIndex), node);
                        }

                        boolean hasSameNextElement = false;
                        if (i < nodeText.getElements().size() - 1 && nextCsmElementIndex < elements.size()) {
                            TextElement nextTextElement = nodeText.getTextElement(i + 1);

                            hasSameNextElement = isCorrespondingElement(nextTextElement, elements.get(nextCsmElementIndex), node);
                        }

                        if (hasSamePreviousElement && hasSameNextElement) {
                            potentialMatches.putIfAbsent(MatchClassification.ALL, i);
                        } else if (hasSamePreviousElement) {
                            potentialMatches.putIfAbsent(MatchClassification.PREVIOUS_AND_SAME, i);
                        } else if (hasSameNextElement) {
                            potentialMatches.putIfAbsent(MatchClassification.NEXT_AND_SAME, i);
                        } else {
                            potentialMatches.putIfAbsent(MatchClassification.SAME_ONLY, i);
                        }
                    }
                }
            }

            // Prioritize the matches from best to worst
            Optional<MatchClassification> bestMatchKey = potentialMatches.keySet().stream()
                    .sorted(Comparator.comparing(MatchClassification::getPriority))
                    .findFirst();

            if (bestMatchKey.isPresent()) {
                correspondingIndices.add(potentialMatches.get(bestMatchKey.get()));
            } else {
                correspondingIndices.add(-1);
            }
        }

        return correspondingIndices;
    }

    private enum MatchClassification {
        ALL(1), PREVIOUS_AND_SAME(2), NEXT_AND_SAME(3), SAME_ONLY(4);

        private final int priority;
        MatchClassification(int priority) {
            this.priority = priority;
        }

        int getPriority() {
            return priority;
        }
    }

    private boolean isCorrespondingElement(TextElement textElement, CsmElement csmElement, Node node) {
        if (csmElement instanceof CsmToken) {
            CsmToken csmToken = (CsmToken)csmElement;
            if (textElement instanceof TokenTextElement) {
                TokenTextElement tokenTextElement = (TokenTextElement)textElement;
                if (tokenTextElement.getTokenKind() == csmToken.getTokenType() && tokenTextElement.getText().equals(csmToken.getContent(node))) {
                    return  true;
                }
            }
        } else if (csmElement instanceof CsmChild) {
            CsmChild csmChild = (CsmChild)csmElement;
            if (textElement instanceof ChildTextElement) {
                ChildTextElement childTextElement = (ChildTextElement)textElement;
                if (childTextElement.getChild() == csmChild.getChild()) {
                    return true;
                }
            }
        } else {
            throw new UnsupportedOperationException();
        }

        return false;
    }

    private int adjustIndentation(List<TokenTextElement> indentation, NodeText nodeText, int nodeTextIndex, boolean followedByUnindent) {
        List<TextElement> indentationAdj = processIndentation(indentation, nodeText.getElements().subList(0, nodeTextIndex - 1));
        if (nodeTextIndex < nodeText.getElements().size() && nodeText.getElements().get(nodeTextIndex).isToken(RBRACE)) {
            indentationAdj = indentationAdj.subList(0, indentationAdj.size() - Math.min(STANDARD_INDENTATION_SIZE, indentationAdj.size()));
        } else if (followedByUnindent) {
            indentationAdj = indentationAdj.subList(0, Math.max(0, indentationAdj.size() - STANDARD_INDENTATION_SIZE));
        }
        for (TextElement e : indentationAdj) {
            if ((nodeTextIndex<nodeText.getElements().size()) && nodeText.getElements().get(nodeTextIndex).isSpaceOrTab()) {
                nodeTextIndex++;
            } else {
                nodeText.getElements().add(nodeTextIndex++, e);
            }
        }
        return nodeTextIndex;
    }

    private boolean isAReplacement(int diffIndex) {
        return (diffIndex > 0) && getElements().get(diffIndex) instanceof Added && getElements().get(diffIndex - 1) instanceof Removed;
    }

    private boolean isPrimitiveType(TextElement textElement) {
        if (textElement instanceof TokenTextElement) {
            TokenTextElement tokenTextElement = (TokenTextElement)textElement;
            int tokenKind = tokenTextElement.getTokenKind();
            return tokenKind == BYTE
                || tokenKind == CHAR
                || tokenKind == SHORT
                || tokenKind == INT
                || tokenKind == LONG
                || tokenKind == FLOAT
                || tokenKind == DOUBLE;
        } else {
            return false;
        }
    }

    private long cost() {
        return elements.stream().filter(e -> !(e instanceof Kept)).count();
    }

    @Override
    public String toString() {
        return "Difference{" + elements + '}';
    }

    public List<DifferenceElement> getElements() {
        return elements;
    }

    /**
     * Remove from the difference all the elements related to indentation.
     * This is mainly intended for test purposes.
     */
    void removeIndentationElements() {
        elements.removeIf(el -> el.getElement() instanceof CsmIndent || el.getElement() instanceof CsmUnindent);
    }
}
