package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.TokenTypes;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;

import java.util.*;
import java.util.stream.Collectors;

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
        // We would calculate the Difference between "qwerty" and "qwer" then we know the A is kep, and then we
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

    private TextElement toTextElement(CsmElement csmElement) {
        if (csmElement instanceof CsmChild) {
            return new ChildTextElement(((CsmChild) csmElement).getChild());
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
        while (nodeTextIndex >=1 && nodeText.getElements().get(nodeTextIndex - 1).isWhiteSpace() && !nodeText.getElements().get(nodeTextIndex - 1).isNewline()) {
            nodeText.removeElement(nodeTextIndex - 1);
            nodeTextIndex--;
        }
        return nodeTextIndex;
    }

    private boolean isAfterLBrace(NodeText nodeText, int nodeTextIndex) {
        if (nodeTextIndex > 0 && nodeText.getElements().get(nodeTextIndex - 1).isToken(LBRACE)) {
            return true;
        }
        if (nodeTextIndex > 0 && nodeText.getElements().get(nodeTextIndex - 1).isWhiteSpace() && !nodeText.getElements().get(nodeTextIndex - 1).isNewline()) {
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
        int diffIndex = 0;
        int nodeTextIndex = 0;
        do {
            if (diffIndex < this.elements.size() && nodeTextIndex >= nodeText.getElements().size()) {
                DifferenceElement diffEl = elements.get(diffIndex);
                if (diffEl instanceof Kept) {
                    Kept kept = (Kept) diffEl;
                    if (kept.element instanceof CsmToken) {
                        CsmToken csmToken = (CsmToken) kept.element;
                        if (TokenTypes.isWhitespaceOrComment(csmToken.getTokenType())) {
                            diffIndex++;
                        } else {
                            throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: "
                                    + nodeText + ". Difference: " + this);
                        }
                    } else {
                        throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: "
                                + nodeText + ". Difference: " + this);
                    }
                } else if (diffEl instanceof Added) {
                    nodeText.addElement(nodeTextIndex, toTextElement(((Added) diffEl).element));
                    nodeTextIndex++;
                    diffIndex++;
                } else {
                    throw new UnsupportedOperationException(diffEl.getClass().getSimpleName());
                }
            } else if (diffIndex >= this.elements.size() && nodeTextIndex < nodeText.getElements().size()) {
                TextElement nodeTextEl = nodeText.getElements().get(nodeTextIndex);
                if (nodeTextEl.isWhiteSpaceOrComment()) {
                    nodeTextIndex++;
                } else {
                    throw new UnsupportedOperationException("NodeText: " + nodeText + ". Difference: "
                            + this + " " + nodeTextEl);
                }
            } else {
                DifferenceElement diffEl = elements.get(diffIndex);
                TextElement nodeTextEl = nodeText.getElements().get(nodeTextIndex);
                if (diffEl instanceof Added) {
                    CsmElement addedElement = ((Added) diffEl).element;
                    if (addedElement instanceof CsmIndent) {
                        for (int i=0;i<STANDARD_INDENTATION_SIZE;i++){
                            indentation.add(new TokenTextElement(GeneratedJavaParserConstants.SPACE));
                        }
                        addedIndentation = true;
                        diffIndex++;
                        continue;
                    }
                    if (addedElement instanceof CsmUnindent) {
                        for (int i=0;i<STANDARD_INDENTATION_SIZE && !indentation.isEmpty();i++){
                            indentation.remove(indentation.size() - 1);
                        }
                        addedIndentation = false;
                        diffIndex++;
                        continue;
                    }
                    TextElement textElement = toTextElement(addedElement);
                    boolean used = false;
                    if (nodeTextIndex > 0 && nodeText.getElements().get(nodeTextIndex - 1).isNewline()) {
                        for (TextElement e : processIndentation(indentation, nodeText.getElements().subList(0, nodeTextIndex - 1))) {
                            nodeText.addElement(nodeTextIndex++, e);
                        }
                    } else if (isAfterLBrace(nodeText, nodeTextIndex) && !isAReplacement(diffIndex)) {
                        if (textElement.isNewline()) {
                            used = true;
                        }
                        nodeText.addElement(nodeTextIndex++, new TokenTextElement(TokenTypes.eolTokenKind()));
                        // This remove the space in "{ }" when adding a new line
                        while (nodeText.getElements().get(nodeTextIndex).isSpaceOrTab()) {
                            nodeText.getElements().remove(nodeTextIndex);
                        }
                        for (TextElement e : processIndentation(indentation, nodeText.getElements().subList(0, nodeTextIndex - 1))) {
                            nodeText.addElement(nodeTextIndex++, e);
                        }
                        // Indentation is painful...
                        // Sometimes we want to force indentation: this is the case when indentation was expected but
                        // was actually not there. For example if we have "{ }" we would expect indentation but it is
                        // not there, so when adding new elements we force it. However if the indentation has been
                        // inserted by us in this transformation we do not want to insert it again
                        if (!addedIndentation) {
                            for (TextElement e : indentationBlock()) {
                                nodeText.addElement(nodeTextIndex++, e);
                            }
                        }
                    }
                    if (!used) {
                        nodeText.addElement(nodeTextIndex, textElement);
                        nodeTextIndex++;
                    }
                    if (textElement.isNewline()) {
                        boolean followedByUnindent = (diffIndex + 1) < elements.size()
                                && elements.get(diffIndex + 1).isAdded()
                                && elements.get(diffIndex + 1).getElement() instanceof CsmUnindent;
                        nodeTextIndex = adjustIndentation(indentation, nodeText, nodeTextIndex, followedByUnindent/* && !addedIndentation*/);
                    }
                    diffIndex++;
                } else if (diffEl instanceof Kept) {
                    Kept kept = (Kept)diffEl;
                    if (nodeTextEl.isComment()) {
                        nodeTextIndex++;
                    } else if ((kept.element instanceof CsmChild) && nodeTextEl instanceof ChildTextElement) {
                        diffIndex++;
                        nodeTextIndex++;
                    } else if ((kept.element instanceof CsmChild) && nodeTextEl instanceof TokenTextElement) {
                        if (nodeTextEl.isWhiteSpaceOrComment()) {
                            nodeTextIndex++;
                        } else {
                            if (kept.element instanceof CsmChild) {
                                CsmChild keptChild = (CsmChild)kept.element;
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
                        } else if (TokenTypes.isWhitespaceOrComment(csmToken.getTokenType())) {
                            diffIndex++;
                        } else if (nodeTextToken.isWhiteSpaceOrComment()) {
                            nodeTextIndex++;
                        } else {
                            throw new UnsupportedOperationException("Csm token " + csmToken + " NodeText TOKEN " + nodeTextToken);
                        }
                    } else if ((kept.element instanceof CsmToken) && ((CsmToken) kept.element).isWhiteSpace()) {
                        diffIndex++;
                    } else if (kept.element instanceof CsmIndent) {
                        // Nothing to do
                        diffIndex++;
                    } else if (kept.element instanceof CsmUnindent) {
                        // Nothing to do, beside considering indentation
                        diffIndex++;
                        for (int i = 0; i < STANDARD_INDENTATION_SIZE && nodeTextIndex >= 1 && nodeText.getTextElement(nodeTextIndex - 1).isSpaceOrTab(); i++) {
                            nodeText.removeElement(--nodeTextIndex);
                        }
                    } else {
                        throw new UnsupportedOperationException("kept " + kept.element + " vs " + nodeTextEl);
                    }
                } else if (diffEl instanceof Removed) {
                    Removed removed = (Removed)diffEl;
                    if ((removed.element instanceof CsmChild) && nodeTextEl instanceof ChildTextElement) {
                        ChildTextElement actualChild = (ChildTextElement)nodeTextEl;
                        if (actualChild.isComment()) {
                            CsmChild csmChild = (CsmChild)removed.element;
                            // We expected to remove a proper node but we found a comment in between.
                            // If the comment is associated to the node we want to remove we remove it as well, otherwise we keep it
                            Comment comment = (Comment)actualChild.getChild();
                            if (!comment.isOrphan() && comment.getCommentedNode().isPresent() && comment.getCommentedNode().get().equals(csmChild.getChild())) {
                                nodeText.removeElement(nodeTextIndex);
                            } else {
                                nodeTextIndex++;
                            }
                        } else {
                            nodeText.removeElement(nodeTextIndex);
                            if (nodeTextIndex < nodeText.getElements().size() && nodeText.getElements().get(nodeTextIndex).isNewline()) {
                                nodeTextIndex = considerCleaningTheLine(nodeText, nodeTextIndex);
                            } else {
                                if (diffIndex + 1 >= this.getElements().size() || !(this.getElements().get(diffIndex + 1) instanceof Added)) {
                                    nodeTextIndex = considerEnforcingIndentation(nodeText, nodeTextIndex);
                                }
                                // If in front we have one space and before also we had space let's drop one space
                                if (nodeText.getElements().size() > nodeTextIndex && nodeTextIndex > 0) {
                                    if (nodeText.getElements().get(nodeTextIndex).isWhiteSpace()
                                            && nodeText.getElements().get(nodeTextIndex - 1).isWhiteSpace()) {
                                        // However we do not want to do that when we are about to adding or removing elements
                                        if ((diffIndex + 1) == this.elements.size() || (elements.get(diffIndex + 1) instanceof Kept)) {
                                            nodeText.getElements().remove(nodeTextIndex--);
                                        }
                                    }
                                }
                            }
                            diffIndex++;
                        }
                    } else if ((removed.element instanceof CsmToken) && nodeTextEl instanceof TokenTextElement
                            && ((CsmToken)removed.element).getTokenType() == ((TokenTextElement)nodeTextEl).getTokenKind()) {
                        nodeText.removeElement(nodeTextIndex);
                        diffIndex++;
                    } else if (nodeTextEl instanceof TokenTextElement
                            && nodeTextEl.isWhiteSpaceOrComment()) {
                        nodeTextIndex++;
                    } else if (removed.element instanceof CsmChild
                            && ((CsmChild)removed.element).getChild() instanceof PrimitiveType) {
                        if (isPrimitiveType(nodeTextEl)) {
                            nodeText.removeElement(nodeTextIndex);
                            diffIndex++;
                        } else {
                            throw new UnsupportedOperationException("removed " + removed.element + " vs " + nodeTextEl);
                        }
                    } else if (removed.element instanceof CsmToken && ((CsmToken)removed.element).isWhiteSpace()) {
                        diffIndex++;
                    } else if (nodeTextEl.isWhiteSpace()) {
                        nodeTextIndex++;
                    } else {
                        throw new UnsupportedOperationException("removed " + removed.element + " vs " + nodeTextEl);
                    }
                } else if (diffEl instanceof Reshuffled) {

                    // First, let's see how many tokens we need to attribute to the previous version of the of the CsmMix
                    Reshuffled reshuffled = (Reshuffled)diffEl;
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
                    final int startNodeTextIndex = nodeTextIndex;
                    final Set<Integer> usedIndexes = new HashSet<>();
                    List<Integer> nodeTextIndexOfPreviousElements = elementsFromPreviousOrder.getElements().stream()
                            .map(it -> findIndexOfCorrespondingNodeTextElement(it, nodeText, startNodeTextIndex, usedIndexes, node))
                            .collect(Collectors.toList());
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
                        for (int ntIndex = startNodeTextIndex; ntIndex<=lastNodeTextIndex; ntIndex++) {

                            if (nodeTextIndexToPreviousCSMIndex.containsKey(ntIndex)) {
                                int indexOfOriginalCSMElement = nodeTextIndexToPreviousCSMIndex.get(ntIndex);
                                if (elementsToAddBeforeGivenOriginalCSMElement.containsKey(indexOfOriginalCSMElement)) {
                                    for (CsmElement elementToAdd : elementsToAddBeforeGivenOriginalCSMElement.get(indexOfOriginalCSMElement)) {
                                        elements.add(diffElIterator++, new Added(elementToAdd));
                                    }
                                }

                                CsmElement originalCSMElement = elementsFromPreviousOrder.getElements().get(indexOfOriginalCSMElement);
                                boolean toBeKept = correspondanceBetweenNextOrderAndPreviousOrder.containsValue(indexOfOriginalCSMElement);
                                if (toBeKept) {
                                    elements.add(diffElIterator++, new Kept(originalCSMElement));
                                } else {
                                    elements.add(diffElIterator++, new Removed(originalCSMElement));
                                }
                            }
                            // else we have a simple node text element, without associated csm element, just keep ignore it
                        }
                    }

                    // Finally we look for the remaining new elements that were not yet added and
                    // add all of them
                    for (CsmElement elementToAdd : elementsToBeAddedAtTheEnd) {
                        elements.add(diffElIterator++, new Added(elementToAdd));
                    }
                } else {
                    throw new UnsupportedOperationException("" + diffEl + " vs " + nodeTextEl);
                }
            }
        } while (diffIndex < this.elements.size() || nodeTextIndex < nodeText.getElements().size());
    }

    private int findIndexOfCorrespondingNodeTextElement(CsmElement csmElement, NodeText nodeText, int startIndex, Set<Integer> usedIndexes, Node node) {
        for (int i=startIndex;i<nodeText.getElements().size();i++){
            if (!usedIndexes.contains(i)) {
                TextElement textElement = nodeText.getTextElement(i);
                if (csmElement instanceof CsmToken) {
                    CsmToken csmToken = (CsmToken)csmElement;
                    if (textElement instanceof TokenTextElement) {
                        TokenTextElement tokenTextElement = (TokenTextElement)textElement;
                        if (tokenTextElement.getTokenKind() == csmToken.getTokenType() && tokenTextElement.getText().equals(csmToken.getContent(node))) {
                            usedIndexes.add(i);
                            return i;
                        }
                    }
                } else if (csmElement instanceof CsmChild) {
                    CsmChild csmChild = (CsmChild)csmElement;
                    if (textElement instanceof ChildTextElement) {
                        ChildTextElement childTextElement = (ChildTextElement)textElement;
                        if (childTextElement.getChild() == csmChild.getChild()) {
                            usedIndexes.add(i);
                            return i;
                        }
                    }
                } else {
                    throw new UnsupportedOperationException();
                }
            }
        }
        return -1;
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
