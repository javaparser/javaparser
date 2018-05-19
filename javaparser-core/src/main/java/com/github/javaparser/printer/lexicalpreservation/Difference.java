package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.Comment;
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

    private final List<DifferenceElementCalculator.DifferenceElement> diffElements;
    private final NodeText nodeText;
    private final Node node;

    private final List<TextElement> originalElements;

    private int originalIndex = 0;
    private int diffIndex = 0;

    Difference(List<DifferenceElementCalculator.DifferenceElement> diffElements, NodeText nodeText, Node node) {
        if (nodeText == null) {
            throw new NullPointerException("nodeText can not be null");
        }

        this.diffElements = diffElements;
        this.nodeText = nodeText;
        this.node = node;

        this.originalElements = nodeText.getElements();
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
        for (int i = nodeTextIndex; i >= 0 && hasOnlyWsBefore && i < nodeText.getElements().size(); i--) {
            if (nodeText.getElements().get(i).isNewline()) {
                break;
            }
            if (!nodeText.getElements().get(i).isSpaceOrTab()) {
                hasOnlyWsBefore = false;
            }
        }
        if (hasOnlyWsBefore) {
            for (int i = nodeTextIndex; i >= 0 && i < nodeText.getElements().size(); i--) {
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
    void apply() {
        boolean addedIndentation = false;
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(node);

        do {
            if (diffIndex < diffElements.size() && originalIndex >= originalElements.size()) {
                DifferenceElementCalculator.DifferenceElement diffElement = diffElements.get(diffIndex);
                if (diffElement instanceof DifferenceElementCalculator.Kept) {
                    DifferenceElementCalculator.Kept kept = (DifferenceElementCalculator.Kept) diffElement;

                    if (kept.isWhiteSpaceOrComment()) {
                        diffIndex++;
                    } else {
                        throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: "
                                + nodeText + ". Difference: " + this);
                    }
                } else if (diffElement instanceof DifferenceElementCalculator.Added) {
                    DifferenceElementCalculator.Added addedElement = (DifferenceElementCalculator.Added) diffElement;

                    nodeText.addElement(originalIndex, addedElement.toTextElement());
                    originalIndex++;
                    diffIndex++;
                } else {
                    throw new UnsupportedOperationException(diffElement.getClass().getSimpleName());
                }
            } else if (diffIndex >= diffElements.size() && originalIndex < originalElements.size()) {
                TextElement originalElement = originalElements.get(originalIndex);

                if (originalElement.isWhiteSpaceOrComment()) {
                    originalIndex++;
                } else {
                    throw new UnsupportedOperationException("NodeText: " + nodeText + ". Difference: "
                            + this + " " + originalElement);
                }
            } else {
                DifferenceElementCalculator.DifferenceElement diffElement = diffElements.get(diffIndex);

                if (diffElement instanceof DifferenceElementCalculator.Added) {
                    DifferenceElementCalculator.Added addedElement = (DifferenceElementCalculator.Added) diffElement;

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

                    TextElement addedTextElement = addedElement.toTextElement();
                    boolean used = false;
                    if (originalIndex > 0 && originalElements.get(originalIndex - 1).isNewline()) {
                        for (TextElement e : processIndentation(indentation, originalElements.subList(0, originalIndex - 1))) {
                            nodeText.addElement(originalIndex++, e);
                        }
                    } else if (isAfterLBrace(nodeText, originalIndex) && !isAReplacement(diffIndex)) {
                        if (addedTextElement.isNewline()) {
                            used = true;
                        }
                        nodeText.addElement(originalIndex++, new TokenTextElement(TokenTypes.eolTokenKind()));
                        // This remove the space in "{ }" when adding a new line
                        while (originalElements.get(originalIndex).isSpaceOrTab()) {
                            originalElements.remove(originalIndex);
                        }
                        for (TextElement e : processIndentation(indentation, originalElements.subList(0, originalIndex - 1))) {
                            nodeText.addElement(originalIndex++, e);
                        }
                        // Indentation is painful...
                        // Sometimes we want to force indentation: this is the case when indentation was expected but
                        // was actually not there. For example if we have "{ }" we would expect indentation but it is
                        // not there, so when adding new elements we force it. However if the indentation has been
                        // inserted by us in this transformation we do not want to insert it again
                        if (!addedIndentation) {
                            for (TextElement e : indentationBlock()) {
                                nodeText.addElement(originalIndex++, e);
                            }
                        }
                    }

                    if (!used) {
                        nodeText.addElement(originalIndex, addedTextElement);
                        originalIndex++;
                    }

                    if (addedTextElement.isNewline()) {
                        boolean followedByUnindent = isFollowedByUnindent(diffElements, diffIndex);
                        originalIndex = adjustIndentation(indentation, nodeText, originalIndex, followedByUnindent/* && !addedIndentation*/);
                    }

                    diffIndex++;
                } else {
                    TextElement originalElement = originalElements.get(originalIndex);
                    boolean originalElementIsChild = originalElement instanceof ChildTextElement;
                    boolean originalElementIsToken = originalElement instanceof TokenTextElement;

                    if (diffElement instanceof DifferenceElementCalculator.Kept) {
                        DifferenceElementCalculator.Kept kept = (DifferenceElementCalculator.Kept)diffElement;

                        if (originalElement.isComment()) {
                            originalIndex++;
                        } else if (kept.isChild() && originalElementIsChild) {
                            diffIndex++;
                            originalIndex++;
                        } else if (kept.isChild() && originalElementIsToken) {
                            if (originalElement.isWhiteSpaceOrComment()) {
                                originalIndex++;
                            } else {
                                if (kept.isPrimitiveType()) {
                                    originalIndex++;
                                    diffIndex++;
                                } else {
                                    throw new UnsupportedOperationException("kept " + kept.element + " vs " + originalElement);
                                }
                            }
                        } else if (kept.isToken() && originalElementIsToken) {
                            TokenTextElement originalTextToken = (TokenTextElement) originalElement;

                            if (kept.getTokenType() == originalTextToken.getTokenKind()) {
                                originalIndex++;
                                diffIndex++;
                            } else if (kept.isWhiteSpaceOrComment()) {
                                diffIndex++;
                            } else if (originalTextToken.isWhiteSpaceOrComment()) {
                                originalIndex++;
                            } else {
                                throw new UnsupportedOperationException("Csm token " + kept.element + " NodeText TOKEN " + originalTextToken);
                            }
                        } else if (kept.isWhiteSpace()) {
                            diffIndex++;
                        } else if (kept.isIndent()) {
                            diffIndex++;
                        } else if (kept.isUnindent()) {
                            // Nothing to do, beside considering indentation
                            diffIndex++;
                            for (int i = 0; i < STANDARD_INDENTATION_SIZE && originalIndex >= 1 && nodeText.getTextElement(originalIndex - 1).isSpaceOrTab(); i++) {
                                nodeText.removeElement(--originalIndex);
                            }
                        } else {
                            throw new UnsupportedOperationException("kept " + kept.element + " vs " + originalElement);
                        }
                    } else if (diffElement instanceof DifferenceElementCalculator.Removed) {
                        DifferenceElementCalculator.Removed removed = (DifferenceElementCalculator.Removed)diffElement;

                        if (removed.isChild() && originalElementIsChild) {
                            ChildTextElement originalElementChild = (ChildTextElement)originalElement;
                            if (originalElementChild.isComment()) {
                                // We expected to remove a proper node but we found a comment in between.
                                // If the comment is associated to the node we want to remove we remove it as well, otherwise we keep it
                                Comment comment = (Comment)originalElementChild.getChild();
                                if (!comment.isOrphan() && comment.getCommentedNode().isPresent() && comment.getCommentedNode().get().equals(removed.getChild())) {
                                    nodeText.removeElement(originalIndex);
                                } else {
                                    originalIndex++;
                                }
                            } else {
                                nodeText.removeElement(originalIndex);
                                if (originalIndex < originalElements.size() && originalElements.get(originalIndex).isNewline()) {
                                    originalIndex = considerCleaningTheLine(nodeText, originalIndex);
                                } else {
                                    if (diffIndex + 1 >= diffElements.size() || !(diffElements.get(diffIndex + 1) instanceof DifferenceElementCalculator.Added)) {
                                        originalIndex = considerEnforcingIndentation(nodeText, originalIndex);
                                    }
                                    // If in front we have one space and before also we had space let's drop one space
                                    if (originalElements.size() > originalIndex && originalIndex > 0) {
                                        if (originalElements.get(originalIndex).isWhiteSpace()
                                                && originalElements.get(originalIndex - 1).isWhiteSpace()) {
                                            // However we do not want to do that when we are about to adding or removing elements
                                            if ((diffIndex + 1) == diffElements.size() || (diffElements.get(diffIndex + 1) instanceof DifferenceElementCalculator.Kept)) {
                                                originalElements.remove(originalIndex--);
                                            }
                                        }
                                    }
                                }
                                diffIndex++;
                            }
                        } else if (removed.isToken() && originalElementIsToken
                                && (removed.getTokenType() == ((TokenTextElement)originalElement).getTokenKind())) {
                            nodeText.removeElement(originalIndex);
                            diffIndex++;
                        } else if (originalElementIsToken && originalElement.isWhiteSpaceOrComment()) {
                            originalIndex++;
                        } else if (removed.isPrimitiveType()) {
                            if (isPrimitiveType(originalElement)) {
                                nodeText.removeElement(originalIndex);
                                diffIndex++;
                            } else {
                                throw new UnsupportedOperationException("removed " + removed.element + " vs " + originalElement);
                            }
                        } else if (removed.isWhiteSpace()) {
                            diffIndex++;
                        } else if (originalElement.isWhiteSpace()) {
                            originalIndex++;
                        } else {
                            throw new UnsupportedOperationException("removed " + removed.element + " vs " + originalElement);
                        }
                    } else if (diffElement instanceof DifferenceElementCalculator.Reshuffled) {
                        // First, let's see how many tokens we need to attribute to the previous version of the of the CsmMix
                        DifferenceElementCalculator.Reshuffled reshuffled = (DifferenceElementCalculator.Reshuffled)diffElement;
                        CsmMix elementsFromPreviousOrder = reshuffled.previousOrder;
                        CsmMix elementsFromNextOrder = reshuffled.element;

                        // This contains indexes from elementsFromNextOrder to indexes from elementsFromPreviousOrder
                        Map<Integer, Integer> correspondanceBetweenNextOrderAndPreviousOrder = getCorrespondanceBetweenNextOrderAndPreviousOrder(elementsFromPreviousOrder, elementsFromNextOrder);

                        // We now find out which Node Text elements corresponds to the elements in the original CSM
                        List<Integer> nodeTextIndexOfPreviousElements = findIndexOfCorrespondingNodeTextElement(elementsFromPreviousOrder.getElements(), nodeText, originalIndex, node);

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
                        List<CsmElement> nextOrderElements = elementsFromNextOrder.getElements();

                        Map<Integer, List<CsmElement>> elementsToAddBeforeGivenOriginalCSMElement = new HashMap<>();
                        for (int ni = 0; ni< nextOrderElements.size(); ni++) {
                            // If it has a mapping, then it is kept
                            if (!correspondanceBetweenNextOrderAndPreviousOrder.containsKey(ni)) {
                                // Ok, it is something new. Where to put it? Let's see what is the first following
                                // element that has a mapping
                                int originalCsmIndex = -1;
                                for (int nj = ni + 1; nj< nextOrderElements.size() && originalCsmIndex==-1; nj++) {
                                    if (correspondanceBetweenNextOrderAndPreviousOrder.containsKey(nj)) {
                                        originalCsmIndex = correspondanceBetweenNextOrderAndPreviousOrder.get(nj);
                                        if (!elementsToAddBeforeGivenOriginalCSMElement.containsKey(originalCsmIndex)){
                                            elementsToAddBeforeGivenOriginalCSMElement.put(originalCsmIndex, new LinkedList<>());
                                        }
                                        elementsToAddBeforeGivenOriginalCSMElement.get(originalCsmIndex).add(nextOrderElements.get(ni));
                                    }
                                }
                                // it does not preceed anything, so it goes at the end
                                if (originalCsmIndex == -1) {
                                    elementsToBeAddedAtTheEnd.add(nextOrderElements.get(ni));
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

                        diffElements.remove(diffIndex);

                        int diffElIterator = diffIndex;
                        if (lastNodeTextIndex != -1) {
                            for (int ntIndex = originalIndex; ntIndex<=lastNodeTextIndex; ntIndex++) {

                                if (nodeTextIndexToPreviousCSMIndex.containsKey(ntIndex)) {
                                    int indexOfOriginalCSMElement = nodeTextIndexToPreviousCSMIndex.get(ntIndex);
                                    if (elementsToAddBeforeGivenOriginalCSMElement.containsKey(indexOfOriginalCSMElement)) {
                                        for (CsmElement elementToAdd : elementsToAddBeforeGivenOriginalCSMElement.get(indexOfOriginalCSMElement)) {
                                            diffElements.add(diffElIterator++, new DifferenceElementCalculator.Added(elementToAdd));
                                        }
                                    }

                                    CsmElement originalCSMElement = elementsFromPreviousOrder.getElements().get(indexOfOriginalCSMElement);
                                    boolean toBeKept = correspondanceBetweenNextOrderAndPreviousOrder.containsValue(indexOfOriginalCSMElement);
                                    if (toBeKept) {
                                        diffElements.add(diffElIterator++, new DifferenceElementCalculator.Kept(originalCSMElement));
                                    } else {
                                        diffElements.add(diffElIterator++, new DifferenceElementCalculator.Removed(originalCSMElement));
                                    }
                                }
                                // else we have a simple node text element, without associated csm element, just keep ignore it
                            }
                        }

                        // Finally we look for the remaining new elements that were not yet added and
                        // add all of them
                        for (CsmElement elementToAdd : elementsToBeAddedAtTheEnd) {
                            diffElements.add(diffElIterator++, new DifferenceElementCalculator.Added(elementToAdd));
                        }
                    } else {
                        throw new UnsupportedOperationException("" + diffElement + " vs " + originalElement);
                    }
                }
            }
        } while (diffIndex < diffElements.size() || originalIndex < originalElements.size());
    }

    private Map<Integer, Integer> getCorrespondanceBetweenNextOrderAndPreviousOrder(CsmMix elementsFromPreviousOrder, CsmMix elementsFromNextOrder) {
        Map<Integer, Integer> correspondanceBetweenNextOrderAndPreviousOrder = new HashMap<>();

        List<CsmElement> nextOrderElements = elementsFromNextOrder.getElements();
        for (int ni = 0; ni< nextOrderElements.size(); ni++) {
            boolean found = false;
            CsmElement ne = nextOrderElements.get(ni);

            List<CsmElement> previousOrderElements = elementsFromPreviousOrder.getElements();
            for (int pi = 0; pi< previousOrderElements.size() && !found; pi++) {
                CsmElement pe = previousOrderElements.get(pi);
                if (!correspondanceBetweenNextOrderAndPreviousOrder.values().contains(pi)
                        && DifferenceElementCalculator.matching(ne, pe)) {
                    found = true;
                    correspondanceBetweenNextOrderAndPreviousOrder.put(ni, pi);
                }
            }
        }

        return correspondanceBetweenNextOrderAndPreviousOrder;
    }

    private boolean isFollowedByUnindent(List<DifferenceElementCalculator.DifferenceElement> diffElements, int diffIndex) {
        return (diffIndex + 1) < diffElements.size()
                && diffElements.get(diffIndex + 1).isAdded()
                && diffElements.get(diffIndex + 1).getElement() instanceof CsmUnindent;
    }

    private List<Integer> findIndexOfCorrespondingNodeTextElement(List<CsmElement> elements, NodeText nodeText, int startIndex, Node node) {
        List<Integer> correspondingIndices = new ArrayList<>();
        for (ListIterator<CsmElement> csmElementListIterator = elements.listIterator(); csmElementListIterator.hasNext(); ) {

            int previousCsmElementIndex = csmElementListIterator.previousIndex();
            CsmElement csmElement = csmElementListIterator.next();
            int nextCsmElementIndex = csmElementListIterator.nextIndex();

            Map<MatchClassification, Integer> potentialMatches = new EnumMap<>(MatchClassification.class);
            for (int i = startIndex; i< nodeText.getElements().size(); i++){
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
                    .min(Comparator.comparing(MatchClassification::getPriority));

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
                return tokenTextElement.getTokenKind() == csmToken.getTokenType() && tokenTextElement.getText().equals(csmToken.getContent(node));
            }
        } else if (csmElement instanceof CsmChild) {
            CsmChild csmChild = (CsmChild)csmElement;
            if (textElement instanceof ChildTextElement) {
                ChildTextElement childTextElement = (ChildTextElement)textElement;
                return childTextElement.getChild() == csmChild.getChild();
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
            if ((nodeTextIndex< nodeText.getElements().size()) && nodeText.getElements().get(nodeTextIndex).isSpaceOrTab()) {
                nodeTextIndex++;
            } else {
                nodeText.getElements().add(nodeTextIndex++, e);
            }
        }
        return nodeTextIndex;
    }

    private boolean isAReplacement(int diffIndex) {
        return (diffIndex > 0) && diffElements.get(diffIndex) instanceof DifferenceElementCalculator.Added && diffElements.get(diffIndex - 1) instanceof DifferenceElementCalculator.Removed;
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
    @Override
    public String toString() {
        return "Difference{" + diffElements + '}';
    }
}
