/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import java.util.*;

public class ReshuffledDiffElementExtractor {

    private final NodeText nodeText;

    private enum MatchClassification {
        ALL(1),
        PREVIOUS_AND_SAME(2),
        NEXT_AND_SAME(3),
        SAME_ONLY(4),
        ALMOST(5);

        private final int priority;

        MatchClassification(int priority) {
            this.priority = priority;
        }

        int getPriority() {
            return priority;
        }
    }

    static ReshuffledDiffElementExtractor of(NodeText nodeText) {
        return new ReshuffledDiffElementExtractor(nodeText);
    }

    private ReshuffledDiffElementExtractor(NodeText nodeText) {
        this.nodeText = nodeText;
    }

    public void extract(List<DifferenceElement> diffElements) {
        IndexTrackingIterator<DifferenceElement> iterator = new IndexTrackingIterator<>(diffElements);
        while (iterator.hasNext()) {
            DifferenceElement diffElement = iterator.next();
            if (diffElement instanceof Reshuffled) {
                Reshuffled reshuffled = (Reshuffled) diffElement;
                // First, let's see how many tokens we need to attribute to the previous version of the of the CsmMix
                CsmMix elementsFromPreviousOrder = reshuffled.getPreviousOrder();
                CsmMix elementsFromNextOrder = reshuffled.getNextOrder();
                // This contains indexes from elementsFromNextOrder to indexes from elementsFromPreviousOrder
                Map<Integer, Integer> correspondanceBetweenNextOrderAndPreviousOrder =
                        getCorrespondanceBetweenNextOrderAndPreviousOrder(
                                elementsFromPreviousOrder, elementsFromNextOrder);
                // We now find out which Node Text elements corresponds to the elements in the original CSM
                List<Integer> nodeTextIndexOfPreviousElements =
                        findIndexOfCorrespondingNodeTextElement(elementsFromPreviousOrder.getElements(), nodeText);
                PeekingIterator<Integer> nodeTextIndexOfPreviousElementsIterator =
                        new PeekingIterator<>(nodeTextIndexOfPreviousElements);
                Map<Integer, Integer> nodeTextIndexToPreviousCSMIndex = new HashMap<>();
                while (nodeTextIndexOfPreviousElementsIterator.hasNext()) {
                    int value = nodeTextIndexOfPreviousElementsIterator.next();
                    if (value != -1) {
                        nodeTextIndexToPreviousCSMIndex.put(
                                value, nodeTextIndexOfPreviousElementsIterator.currentIndex());
                    }
                }
                int lastNodeTextIndex = nodeTextIndexOfPreviousElements.stream()
                        .max(Integer::compareTo)
                        .orElse(-1);
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
                                    elementsToAddBeforeGivenOriginalCSMElement.put(
                                            originalCsmIndex, new LinkedList<>());
                                }
                                elementsToAddBeforeGivenOriginalCSMElement
                                        .get(originalCsmIndex)
                                        .add(nextOrderElements.get(ni));
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
                // we find the correspond OCE (Original CSM Element)
                // * we first add new elements that are marked to be added before OCE
                // * if OCE is marked to be present also in the "after" CSM we add a kept element,
                // otherwise we add a removed element
                // Remove the whole Reshuffled element
                iterator.remove();
                if (lastNodeTextIndex != -1) {
                    for (int ntIndex = 0; ntIndex <= lastNodeTextIndex; ntIndex++) {
                        if (nodeTextIndexToPreviousCSMIndex.containsKey(ntIndex)) {
                            int indexOfOriginalCSMElement = nodeTextIndexToPreviousCSMIndex.get(ntIndex);
                            if (elementsToAddBeforeGivenOriginalCSMElement.containsKey(indexOfOriginalCSMElement)) {
                                for (CsmElement elementToAdd :
                                        elementsToAddBeforeGivenOriginalCSMElement.get(indexOfOriginalCSMElement)) {
                                    iterator.add(new Added(elementToAdd));
                                }
                            }
                            CsmElement originalCSMElement =
                                    elementsFromPreviousOrder.getElements().get(indexOfOriginalCSMElement);
                            boolean toBeKept = correspondanceBetweenNextOrderAndPreviousOrder.containsValue(
                                    indexOfOriginalCSMElement);
                            if (toBeKept) {
                                iterator.add(new Kept(originalCSMElement));
                            } else {
                                iterator.add(new Removed(originalCSMElement));
                            }
                        }
                        // else we have a simple node text element, without associated csm element, just keep ignore it
                    }
                }
                // Finally we look for the remaining new elements that were not yet added and
                // add all of them
                for (CsmElement elementToAdd : elementsToBeAddedAtTheEnd) {
                    iterator.add(new Added(elementToAdd));
                }
            }
        }
    }

    /*
     * Computes which elements of the previous order (the CsmMix before the change, L1) are still present in the
     * next order (the CsmMix after the change, L2). The result maps an index of L2 to the index of the
     * corresponding element of L1. An element of L1 without correspondence is removed, an element of L2 without
     * correspondence is added, the others are kept.
     *
     * Both lists are ordered, so the correspondence must preserve the order: if a is matched with a' and b with
     * b', a before b in L2 implies a' before b' in L1.
     *
     * The child nodes and the tokens are not matched in the same way:
     * - a child node is unique: it identifies without ambiguity a position in both lists, so it anchors the
     *   correspondence;
     * - a token (end of line, space, separator...) is not: the same token usually appears several times, after
     *   each child node. Matched first, a token can be paired with the wrong occurrence.
     *
     * For example, when removing @A from [@A, eol, @B, eol], which becomes [@B, eol], a single left-to-right
     * pass pairs the first end of line of L1 (the one following the removed @A) with the end of line of L2, then
     * no longer finds @B after it: @B would be considered as removed and added again, which moves it and loses
     * its comment. The expected correspondence is @B with @B and the end of line of L2 with the one following
     * @B in L1.
     *
     * The correspondence is therefore computed in two steps:
     * 1. the child nodes are matched, in order;
     * 2. each token of L2 is matched with a token of L1 located between the child nodes surrounding it, i.e.
     *    after the element of L1 matched with the previous child node of L2 and before the element of L1
     *    matched with the next child node of L2, in order.
     */
    private Map<Integer, Integer> getCorrespondanceBetweenNextOrderAndPreviousOrder(
            CsmMix elementsFromPreviousOrder, CsmMix elementsFromNextOrder) {
        Map<Integer, Integer> correspondanceBetweenNextOrderAndPreviousOrder = new HashMap<>();
        List<CsmElement> previousOrderElements = elementsFromPreviousOrder.getElements();
        List<CsmElement> nextOrderElements = elementsFromNextOrder.getElements();
        // Step 1: match the child nodes. For each child node of L1, the search in L2 starts after the last matched
        // child node (syncNextIndex), so that the order is preserved. A child node of L1 that is not found has
        // been removed.
        int syncNextIndex = 0;
        for (int pi = 0; pi < previousOrderElements.size(); pi++) {
            CsmElement pe = previousOrderElements.get(pi);
            if (!(pe instanceof LexicalDifferenceCalculator.CsmChild)) {
                continue;
            }
            for (int ni = syncNextIndex; ni < nextOrderElements.size(); ni++) {
                if (DifferenceElementCalculator.matching(nextOrderElements.get(ni), pe)) {
                    correspondanceBetweenNextOrderAndPreviousOrder.put(ni, pi);
                    syncNextIndex = ni + 1;
                    break;
                }
            }
        }
        // Step 2: match the tokens of L2 between the anchors found in step 1.
        // syncPreviousIndex is the first index of L1 that can still be matched: it follows the last element of L1
        // matched so far (child node or token), so that the order is preserved.
        int syncPreviousIndex = 0;
        for (int ni = 0; ni < nextOrderElements.size(); ni++) {
            Integer anchor = correspondanceBetweenNextOrderAndPreviousOrder.get(ni);
            if (anchor != null) {
                // a child node matched in step 1: the following tokens must be searched after it in L1
                syncPreviousIndex = anchor + 1;
                continue;
            }
            // the search in L1 stops at the element matched with the next child node of L2, if any: a token
            // located before that child node in L2 cannot correspond to a token located after it in L1
            int limit = previousOrderElements.size();
            for (int nj = ni + 1; nj < nextOrderElements.size(); nj++) {
                if (correspondanceBetweenNextOrderAndPreviousOrder.containsKey(nj)) {
                    limit = correspondanceBetweenNextOrderAndPreviousOrder.get(nj);
                    break;
                }
            }
            // first token of L1 in [syncPreviousIndex, limit) matching the token of L2; if there is none, the
            // token of L2 is new (added)
            for (int pi = syncPreviousIndex; pi < limit; pi++) {
                CsmElement pe = previousOrderElements.get(pi);
                if (!(pe instanceof LexicalDifferenceCalculator.CsmChild)
                        && DifferenceElementCalculator.matching(nextOrderElements.get(ni), pe)) {
                    correspondanceBetweenNextOrderAndPreviousOrder.put(ni, pi);
                    syncPreviousIndex = pi + 1;
                    break;
                }
            }
        }
        return correspondanceBetweenNextOrderAndPreviousOrder;
    }

    private List<Integer> findIndexOfCorrespondingNodeTextElement(List<CsmElement> elements, NodeText nodeText) {
        List<Integer> correspondingIndices = new ArrayList<>();
        PeekingIterator<CsmElement> csmElementListIterator = new PeekingIterator<>(elements);
        while (csmElementListIterator.hasNext()) {
            boolean isFirstIterationOnCsmElements = !csmElementListIterator.hasPrevious();
            int previousCsmElementIndex = csmElementListIterator.previousIndex();
            CsmElement csmElement = csmElementListIterator.next();
            Map<MatchClassification, Integer> potentialMatches = new EnumMap<>(MatchClassification.class);
            PeekingIterator<TextElement> nodeTextListIterator = new PeekingIterator<>(nodeText.getElements());
            while (nodeTextListIterator.hasNext()) {
                boolean isFirstIterationOnNodeTextElements = !nodeTextListIterator.hasPrevious();
                TextElement textElement = nodeTextListIterator.next();
                int currentTextElementIndex = nodeTextListIterator.currentIndex();
                if (!correspondingIndices.contains(currentTextElementIndex)) {
                    boolean isCorresponding = csmElement.isCorrespondingElement(textElement);
                    if (isCorresponding) {
                        boolean hasSamePreviousElement = false;
                        if (!isFirstIterationOnNodeTextElements && !isFirstIterationOnCsmElements) {
                            TextElement previousTextElement = nodeText.getTextElement(currentTextElementIndex - 1);
                            hasSamePreviousElement =
                                    elements.get(previousCsmElementIndex).isCorrespondingElement(previousTextElement);
                        }
                        boolean hasSameNextElement = false;
                        if (csmElementListIterator.hasNext()) {
                            TextElement nextTextElement = nodeTextListIterator.peek();
                            hasSameNextElement = elements.get(csmElementListIterator.nextIndex())
                                    .isCorrespondingElement(nextTextElement);
                        }
                        if (hasSamePreviousElement && hasSameNextElement) {
                            potentialMatches.putIfAbsent(MatchClassification.ALL, currentTextElementIndex);
                        } else if (hasSamePreviousElement) {
                            potentialMatches.putIfAbsent(
                                    MatchClassification.PREVIOUS_AND_SAME, currentTextElementIndex);
                        } else if (hasSameNextElement) {
                            potentialMatches.putIfAbsent(MatchClassification.NEXT_AND_SAME, currentTextElementIndex);
                        } else {
                            potentialMatches.putIfAbsent(MatchClassification.SAME_ONLY, currentTextElementIndex);
                        }
                    } else if (isAlmostCorrespondingElement(textElement, csmElement)) {
                        potentialMatches.putIfAbsent(MatchClassification.ALMOST, currentTextElementIndex);
                    }
                }
            }
            // Prioritize the matches from best to worst
            Optional<MatchClassification> bestMatchKey =
                    potentialMatches.keySet().stream().min(Comparator.comparing(MatchClassification::getPriority));
            if (bestMatchKey.isPresent()) {
                correspondingIndices.add(potentialMatches.get(bestMatchKey.get()));
            } else {
                correspondingIndices.add(-1);
            }
        }
        return correspondingIndices;
    }

    private boolean isAlmostCorrespondingElement(TextElement textElement, CsmElement csmElement) {
        if (csmElement.isCorrespondingElement(textElement)) {
            return false;
        }
        return textElement.isWhiteSpace() && csmElement instanceof CsmToken && ((CsmToken) csmElement).isWhiteSpace();
    }
}
