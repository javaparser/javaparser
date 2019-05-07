package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.GeneratedJavaParserConstants.*;

import java.util.*;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.concretesyntaxmodel.CsmUnindent;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;

/**
 * A Difference should give me a sequence of elements I should find (to indicate the context) followed by a list of elements
 * to remove or to add and follow by another sequence of elements.
 *
 * I should later be able to apply such difference to a nodeText.
 */
public class Difference {

    public static final int STANDARD_INDENTATION_SIZE = 4;

    private final NodeText nodeText;
    private final Node node;

    private final List<DifferenceElement> diffElements;
    private final List<TextElement> originalElements;
    private int originalIndex = 0;
    private int diffIndex = 0;

    private final List<TokenTextElement> indentation;
    private boolean addedIndentation = false;

    Difference(List<DifferenceElement> diffElements, NodeText nodeText, Node node) {
        if (nodeText == null) {
            throw new NullPointerException("nodeText can not be null");
        }

        this.nodeText = nodeText;
        this.node = node;
        this.diffElements = diffElements;
        this.originalElements = nodeText.getElements();

        this.indentation = LexicalPreservingPrinter.findIndentation(node);
    }

    private List<TextElement> processIndentation(List<TokenTextElement> indentation, List<TextElement> prevElements) {
        List<TextElement> res = new LinkedList<>(indentation);
        boolean afterNl = false;
        for (TextElement e : prevElements) {
            if (e.isNewline()) {
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
        int res = nodeTextIndex;
        if (hasOnlyWsBefore) {
            for (int i = nodeTextIndex; i >= 0 && i < nodeText.getElements().size(); i--) {
                if (nodeText.getElements().get(i).isNewline()) {
                    break;
                }
                nodeText.removeElement(i);
                res = i;
            }
        }
        if (res < 0) {
            throw new IllegalStateException();
        }
        return res;
    }

    /**
     * Node that we have calculate the Difference we can apply to a concrete NodeText, modifying it according
     * to the difference (adding and removing the elements provided).
     */
    void apply() {
        extractReshuffledDiffElements(diffElements);
        Map<Removed, RemovedGroup> removedGroups = combineRemovedElementsToRemovedGroups();

        do {
            boolean isLeftOverDiffElement = applyLeftOverDiffElements();
            boolean isLeftOverOriginalElement = applyLeftOverOriginalElements();

            if (!isLeftOverDiffElement && !isLeftOverOriginalElement){
                DifferenceElement diffElement = diffElements.get(diffIndex);

                if (diffElement instanceof Added) {
                    applyAddedDiffElement((Added) diffElement);
                } else {
                    TextElement originalElement = originalElements.get(originalIndex);
                    boolean originalElementIsChild = originalElement instanceof ChildTextElement;
                    boolean originalElementIsToken = originalElement instanceof TokenTextElement;

                    if (diffElement instanceof Kept) {
                        applyKeptDiffElement((Kept) diffElement, originalElement, originalElementIsChild, originalElementIsToken);
                    } else if (diffElement instanceof Removed) {
                        Removed removed = (Removed) diffElement;
                        applyRemovedDiffElement(removedGroups.get(removed), removed, originalElement, originalElementIsChild, originalElementIsToken);
                    } else {
                        throw new UnsupportedOperationException("" + diffElement + " vs " + originalElement);
                    }
                }
            }
        } while (diffIndex < diffElements.size() || originalIndex < originalElements.size());
    }

    private boolean applyLeftOverOriginalElements() {
        boolean isLeftOverElement = false;
        if (diffIndex >= diffElements.size() && originalIndex < originalElements.size()) {
            TextElement originalElement = originalElements.get(originalIndex);

            if (originalElement.isWhiteSpaceOrComment()) {
                originalIndex++;
            } else {
                throw new UnsupportedOperationException("NodeText: " + nodeText + ". Difference: "
                        + this + " " + originalElement);
            }

            isLeftOverElement = true;
        }
        return isLeftOverElement;
    }

    private boolean applyLeftOverDiffElements() {
        boolean isLeftOverElement = false;
        if (diffIndex < diffElements.size() && originalIndex >= originalElements.size()) {
            DifferenceElement diffElement = diffElements.get(diffIndex);
            if (diffElement instanceof Kept) {
                Kept kept = (Kept) diffElement;

                if (kept.isWhiteSpaceOrComment() || kept.isIndent() || kept.isUnindent()) {
                    diffIndex++;
                } else {
                    throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: "
                            + nodeText + ". Difference: " + this);
                }
            } else if (diffElement instanceof Added) {
                Added addedElement = (Added) diffElement;

                nodeText.addElement(originalIndex, addedElement.toTextElement());
                originalIndex++;
                diffIndex++;
            } else {
                throw new UnsupportedOperationException(diffElement.getClass().getSimpleName());
            }

            isLeftOverElement = true;
        }

        return isLeftOverElement;
    }

    private void extractReshuffledDiffElements(List<DifferenceElement> diffElements) {
        for (int index = 0; index < diffElements.size(); index++) {
            DifferenceElement diffElement = diffElements.get(index);
            if (diffElement instanceof Reshuffled) {
                Reshuffled reshuffled = (Reshuffled) diffElement;

                // First, let's see how many tokens we need to attribute to the previous version of the of the CsmMix
                CsmMix elementsFromPreviousOrder = reshuffled.getPreviousOrder();
                CsmMix elementsFromNextOrder = reshuffled.getNextOrder();

                // This contains indexes from elementsFromNextOrder to indexes from elementsFromPreviousOrder
                Map<Integer, Integer> correspondanceBetweenNextOrderAndPreviousOrder = getCorrespondanceBetweenNextOrderAndPreviousOrder(elementsFromPreviousOrder, elementsFromNextOrder);

                // We now find out which Node Text elements corresponds to the elements in the original CSM
                List<Integer> nodeTextIndexOfPreviousElements = findIndexOfCorrespondingNodeTextElement(elementsFromPreviousOrder.getElements(), nodeText, originalIndex, node);

                Map<Integer, Integer> nodeTextIndexToPreviousCSMIndex = new HashMap<>();
                for (int i = 0; i < nodeTextIndexOfPreviousElements.size(); i++) {
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
                for (int ni = 0; ni < nextOrderElements.size(); ni++) {
                    // If it has a mapping, then it is kept
                    if (!correspondanceBetweenNextOrderAndPreviousOrder.containsKey(ni)) {
                        // Ok, it is something new. Where to put it? Let's see what is the first following
                        // element that has a mapping
                        int originalCsmIndex = -1;
                        for (int nj = ni + 1; nj < nextOrderElements.size() && originalCsmIndex == -1; nj++) {
                            if (correspondanceBetweenNextOrderAndPreviousOrder.containsKey(nj)) {
                                originalCsmIndex = correspondanceBetweenNextOrderAndPreviousOrder.get(nj);
                                if (!elementsToAddBeforeGivenOriginalCSMElement.containsKey(originalCsmIndex)) {
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

                // Remove the whole Reshuffled element
                diffElements.remove(index);

                int diffElIterator = index;
                if (lastNodeTextIndex != -1) {
                    for (int ntIndex = originalIndex; ntIndex <= lastNodeTextIndex; ntIndex++) {

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
            }
        }
    }

    /**
     * Maps all Removed elements as keys to their corresponding RemovedGroup.
     * A RemovedGroup contains all consecutive Removed elements.
     * <br/>
     * Example:
     * <pre>
     * Elements: Kept|Removed1|Removed2|Kept|Removed3|Added|Removed4
     * Groups:        <----Group1---->       Group2         Group3
     * Keys:          Removed1+Removed2      Removed3       Removed4
     * </pre>
     *
     * @return Map with all Removed elements as keys to their corresponding RemovedGroup
     */
    private Map<Removed, RemovedGroup> combineRemovedElementsToRemovedGroups() {
        Map<Integer, List<Removed>> removedElementsMap = groupConsecutiveRemovedElements();

        List<RemovedGroup> removedGroups = new ArrayList<>();
        for (Map.Entry<Integer, List<Removed>> entry : removedElementsMap.entrySet()) {
            removedGroups.add(RemovedGroup.of(entry.getKey(), entry.getValue()));
        }

        Map<Removed, RemovedGroup> map = new HashMap<>();
        for (RemovedGroup removedGroup : removedGroups){
            for (Removed index : removedGroup) {
                map.put(index, removedGroup);
            }
        }

        return map;
    }

    private Map<Integer, List<Removed>> groupConsecutiveRemovedElements() {
        Map<Integer, List<Removed>> removedElementsMap = new HashMap<>();

        Integer firstElement = null;
        for (int i = 0; i < diffElements.size(); i++) {
            DifferenceElement diffElement = diffElements.get(i);
            if (diffElement instanceof Removed) {
                if (firstElement == null) {
                    firstElement = i;
                }

                removedElementsMap.computeIfAbsent(firstElement, key -> new ArrayList<>())
                        .add((Removed) diffElement);
            } else {
                firstElement = null;
            }
        }
        return removedElementsMap;
    }

    private void applyRemovedDiffElement(RemovedGroup removedGroup, Removed removed, TextElement originalElement, boolean originalElementIsChild, boolean originalElementIsToken) {
        if (removed.isChild() && originalElementIsChild) {
            ChildTextElement originalElementChild = (ChildTextElement) originalElement;
            if (originalElementChild.isComment()) {
                // We expected to remove a proper node but we found a comment in between.
                // If the comment is associated to the node we want to remove we remove it as well, otherwise we keep it
                Comment comment = (Comment) originalElementChild.getChild();
                if (!comment.isOrphan() && comment.getCommentedNode().isPresent() && comment.getCommentedNode().get().equals(removed.getChild())) {
                    nodeText.removeElement(originalIndex);
                } else {
                    originalIndex++;
                }
            } else {
                nodeText.removeElement(originalIndex);

                if ((diffIndex + 1 >= diffElements.size() || !(diffElements.get(diffIndex + 1) instanceof Added))
                        && !removedGroup.isACompleteLine()) {
                    originalIndex = considerEnforcingIndentation(nodeText, originalIndex);
                }
                // If in front we have one space and before also we had space let's drop one space
                if (originalElements.size() > originalIndex && originalIndex > 0) {
                    if (originalElements.get(originalIndex).isWhiteSpace()
                            && originalElements.get(originalIndex - 1).isWhiteSpace()) {
                        // However we do not want to do that when we are about to adding or removing elements
                        if ((diffIndex + 1) == diffElements.size() || (diffElements.get(diffIndex + 1) instanceof Kept)) {
                            originalElements.remove(originalIndex--);
                        }
                    }
                }

                diffIndex++;
            }
        } else if (removed.isToken() && originalElementIsToken &&
                (removed.getTokenType() == ((TokenTextElement) originalElement).getTokenKind()
                        // handle EOLs separately as their token kind might not be equal. This is because the 'removed'
                        // element always has the current operating system's EOL as type
                        || (((TokenTextElement) originalElement).getToken().getCategory().isEndOfLine()
                                && removed.isNewLine()))) {
            nodeText.removeElement(originalIndex);
            diffIndex++;
        } else if (originalElementIsToken && originalElement.isWhiteSpaceOrComment()) {
            originalIndex++;
        } else if (removed.isPrimitiveType()) {
            if (isPrimitiveType(originalElement)) {
                nodeText.removeElement(originalIndex);
                diffIndex++;
            } else {
                throw new UnsupportedOperationException("removed " + removed.getElement() + " vs " + originalElement);
            }
        } else if (removed.isWhiteSpace() || removed.getElement() instanceof CsmIndent || removed.getElement() instanceof CsmUnindent) {
            diffIndex++;
        } else if (originalElement.isWhiteSpace()) {
            originalIndex++;
        } else {
            throw new UnsupportedOperationException("removed " + removed.getElement() + " vs " + originalElement);
        }

        cleanTheLineOfLeftOverSpace(removedGroup, removed);
    }

    /**
     * Cleans the line of left over space if there is unnecessary indentation and the element will not be replaced
     */
    private void cleanTheLineOfLeftOverSpace(RemovedGroup removedGroup, Removed removed) {
        if (originalIndex >= originalElements.size()) {
            // if all elements were already processed there is nothing to do
            return;
        }

        if (!removedGroup.isProcessed()
                && removedGroup.getLastElement() == removed
                && removedGroup.isACompleteLine()) {
            Integer lastElementIndex = removedGroup.getLastElementIndex();
            Optional<Integer> indentation = removedGroup.getIndentation();

            if (indentation.isPresent() && !isReplaced(lastElementIndex)) {
                for (int i = 0; i < indentation.get(); i++) {
                    if (originalElements.get(originalIndex).isSpaceOrTab()) {
                        // If the current element is a space, remove it
                        nodeText.removeElement(originalIndex);
                    } else if (originalIndex >= 1 && originalElements.get(originalIndex - 1).isSpaceOrTab()) {
                        // If the current element is not a space itself we remove the space in front of it
                        nodeText.removeElement(originalIndex - 1);
                        originalIndex--;
                    }
                }
            }

            // Mark RemovedGroup as processed
            removedGroup.processed();
        }
    }

    private void applyKeptDiffElement(Kept kept, TextElement originalElement, boolean originalElementIsChild, boolean originalElementIsToken) {
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
                    throw new UnsupportedOperationException("kept " + kept.getElement() + " vs " + originalElement);
                }
            }
        } else if (kept.isToken() && originalElementIsToken) {
            TokenTextElement originalTextToken = (TokenTextElement) originalElement;

            if (kept.getTokenType() == originalTextToken.getTokenKind()) {
                originalIndex++;
                diffIndex++;
            } else if (kept.isNewLine() && originalTextToken.isSpaceOrTab()) {
                originalIndex++;
                diffIndex++;
            } else if (kept.isWhiteSpaceOrComment()) {
                diffIndex++;
            } else if (originalTextToken.isWhiteSpaceOrComment()) {
                originalIndex++;
            } else {
                throw new UnsupportedOperationException("Csm token " + kept.getElement() + " NodeText TOKEN " + originalTextToken);
            }
        } else if (kept.isWhiteSpace()) {
            diffIndex++;
        } else if (kept.isIndent()) {
            diffIndex++;
        } else if (kept.isUnindent()) {
            // Nothing to do, beside considering indentation
            // However we want to consider the case in which the indentation was not applied, like when we have
            // just a left brace followed by space

            diffIndex++;
            if (!openBraceWasOnSameLine()) {
                for (int i = 0; i < STANDARD_INDENTATION_SIZE && originalIndex >= 1 && nodeText.getTextElement(originalIndex - 1).isSpaceOrTab(); i++) {
                    nodeText.removeElement(--originalIndex);
                }
            }
        } else {
            throw new UnsupportedOperationException("kept " + kept.getElement() + " vs " + originalElement);
        }
    }

    private boolean openBraceWasOnSameLine() {
        int index = originalIndex;
        while (index >= 0 && !nodeText.getTextElement(index).isNewline()) {
            if (nodeText.getTextElement(index).isToken(LBRACE)) {
                return true;
            }
            index--;
        }
        return false;
    }

    private boolean wasSpaceBetweenBraces() {
        return nodeText.getTextElement(originalIndex).isToken(RBRACE)
                && doWeHaveLeftBraceFollowedBySpace(originalIndex - 1)
                && (diffIndex < 2 || !diffElements.get(diffIndex - 2).isRemoved());
    }

    private boolean doWeHaveLeftBraceFollowedBySpace(int index) {
        index = rewindSpace(index);
        return nodeText.getElements().get(index).isToken(LBRACE);
    }

    private int rewindSpace(int index) {
        if (index <= 0) {
            return index;
        }
        if (nodeText.getElements().get(index).isWhiteSpace()) {
            return rewindSpace(index - 1);
        } else {
            return index;
        }
    }

    private boolean nextIsRightBrace(int index) {
        List<TextElement> elements = originalElements.subList(index, originalElements.size());
        for(TextElement element : elements) {
            if (!element.isSpaceOrTab()) {
                return element.isToken(RBRACE);
            }
        }
        return false;
    }

    private void applyAddedDiffElement(Added added) {
        if (added.isIndent()) {
            for (int i=0;i<STANDARD_INDENTATION_SIZE;i++){
                indentation.add(new TokenTextElement(GeneratedJavaParserConstants.SPACE));
            }
            addedIndentation = true;
            diffIndex++;
            return;
        }
        if (added.isUnindent()) {
            for (int i = 0; i<STANDARD_INDENTATION_SIZE && !indentation.isEmpty(); i++){
                indentation.remove(indentation.size() - 1);
            }
            addedIndentation = false;
            diffIndex++;
            return;
        }

        TextElement addedTextElement = added.toTextElement();
        boolean used = false;
        if (originalIndex > 0 && originalElements.get(originalIndex - 1).isNewline()) {
            List<TextElement> elements = processIndentation(indentation, originalElements.subList(0, originalIndex - 1));
            boolean nextIsRightBrace = nextIsRightBrace(originalIndex);
            for (TextElement e : elements) {
                if (!nextIsRightBrace
                        && e instanceof TokenTextElement
                        && originalElements.get(originalIndex).isToken(((TokenTextElement)e).getTokenKind())) {
                    originalIndex++;
                } else {
                    nodeText.addElement(originalIndex++, e);
                }
            }
        } else if (isAfterLBrace(nodeText, originalIndex) && !isAReplacement(diffIndex)) {
            if (addedTextElement.isNewline()) {
                used = true;
            }
            nodeText.addElement(originalIndex++, new TokenTextElement(TokenTypes.eolTokenKind()));
            // This remove the space in "{ }" when adding a new line
            while (originalIndex >= 2 && originalElements.get(originalIndex - 2).isSpaceOrTab()) {
                originalElements.remove(originalIndex - 2);
                originalIndex--;
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
            // Handling trailing comments
            if(nodeText.numberOfElements() > originalIndex + 1 &&
                    nodeText.getTextElement(originalIndex).isComment()) {
                // Need to get behind the comment:
                originalIndex += 2;
                nodeText.addElement(originalIndex, addedTextElement); // Defer originalIndex increment
                // We want to adjust the indentation while considering the new element that we added
                originalIndex = adjustIndentation(indentation, nodeText, originalIndex, false);
                originalIndex++; // Now we can increment
            } else {
                nodeText.addElement(originalIndex, addedTextElement);
                originalIndex++;
            }
        }

        if (addedTextElement.isNewline()) {
            boolean followedByUnindent = isFollowedByUnindent(diffElements, diffIndex);
            boolean nextIsRightBrace = nextIsRightBrace(originalIndex);
            boolean nextIsNewLine = nodeText.getTextElement(originalIndex).isNewline();
            if ((!nextIsNewLine && !nextIsRightBrace) || followedByUnindent) {
                originalIndex = adjustIndentation(indentation, nodeText, originalIndex, followedByUnindent);
            }
        }

        diffIndex++;
    }

    private Map<Integer, Integer> getCorrespondanceBetweenNextOrderAndPreviousOrder(CsmMix elementsFromPreviousOrder, CsmMix elementsFromNextOrder) {
        Map<Integer, Integer> correspondanceBetweenNextOrderAndPreviousOrder = new HashMap<>();

        List<CsmElement> nextOrderElements = elementsFromNextOrder.getElements();
        List<CsmElement> previousOrderElements = elementsFromPreviousOrder.getElements();
        WrappingRangeIterator piNext = new WrappingRangeIterator(previousOrderElements.size());

        for (int ni = 0; ni < nextOrderElements.size(); ni++) {
            boolean found = false;
            CsmElement ne = nextOrderElements.get(ni);

            for (int counter = 0; counter < previousOrderElements.size() && !found; counter++) {
                Integer pi = piNext.next();
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

    private boolean isFollowedByUnindent(List<DifferenceElement> diffElements, int diffIndex) {
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
            for (int i = startIndex; i < nodeText.getElements().size(); i++){
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
                    } else if (isAlmostCorrespondingElement(textElement, csmElement, node)) {
                        potentialMatches.putIfAbsent(MatchClassification.ALMOST, i);
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
        ALL(1), PREVIOUS_AND_SAME(2), NEXT_AND_SAME(3), SAME_ONLY(4), ALMOST(5);

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

    private boolean isAlmostCorrespondingElement(TextElement textElement, CsmElement csmElement, Node node) {
        if (isCorrespondingElement(textElement, csmElement, node)) {
            return false;
        }
        return textElement.isWhiteSpace() && csmElement instanceof CsmToken && ((CsmToken)csmElement).isWhiteSpace();
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
        if (nodeTextIndex < 0) {
            throw new IllegalStateException();
        }
        return nodeTextIndex;
    }

    private boolean isAReplacement(int diffIndex) {
        return (diffIndex > 0) && diffElements.get(diffIndex) instanceof Added && diffElements.get(diffIndex - 1) instanceof Removed;
    }

    private boolean isReplaced(int diffIndex) {
        return (diffIndex < diffElements.size() - 1) && diffElements.get(diffIndex + 1) instanceof Added && diffElements.get(diffIndex) instanceof Removed;
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
