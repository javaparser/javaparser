package com.github.javaparser.printer.lexicalpreservation;

import java.util.*;

import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.lexicalpreservation.Difference.ArrayIterator;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;

public class ReshuffledDiffElementExtractor {

	private final NodeText nodeText;

    private final Node node;

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

    static ReshuffledDiffElementExtractor of(NodeText nodeText, Node node) {
    	return new ReshuffledDiffElementExtractor(nodeText, node);
    }

	private ReshuffledDiffElementExtractor(NodeText nodeText, Node node) {
		this.nodeText = nodeText;
		this.node = node;
	}

	public void extract(List<DifferenceElement> diffElements) {
		int originalIndex = 0;
    	ArrayIterator<DifferenceElement> iterator = new ArrayIterator(diffElements);
        while (iterator.hasNext()) {
            DifferenceElement diffElement = iterator.next();
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
                // we find the correspond OCE (Original CSM Element)
                // * we first add new elements that are marked to be added before OCE
                // * if OCE is marked to be present also in the "after" CSM we add a kept element,
                // otherwise we add a removed element
                // Remove the whole Reshuffled element
                iterator.remove();
                if (lastNodeTextIndex != -1) {
                    for (int ntIndex = originalIndex; ntIndex <= lastNodeTextIndex; ntIndex++) {
                        if (nodeTextIndexToPreviousCSMIndex.containsKey(ntIndex)) {
                            int indexOfOriginalCSMElement = nodeTextIndexToPreviousCSMIndex.get(ntIndex);
                            if (elementsToAddBeforeGivenOriginalCSMElement.containsKey(indexOfOriginalCSMElement)) {
                                for (CsmElement elementToAdd : elementsToAddBeforeGivenOriginalCSMElement.get(indexOfOriginalCSMElement)) {
                                    iterator.add(new Added(elementToAdd));
                                }
                            }
                            CsmElement originalCSMElement = elementsFromPreviousOrder.getElements().get(indexOfOriginalCSMElement);
                            boolean toBeKept = correspondanceBetweenNextOrderAndPreviousOrder.containsValue(indexOfOriginalCSMElement);
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
	 * Considering that the lists of elements are ordered, We can find the common
	 * elements by starting with the list before the modifications and, for each
	 * element, by going through the list of elements containing the modifications.
	 *
	 * We can find the common elements by starting with the list before the
	 * modifications (L1) and, for each element, by going through the list of elements
	 * containing the modifications (L2).
	 *
	 * If element A in list L1 is not found in list L2, it is a deleted element.
	 * If element A of list L1 is found in list L2, it is a kept element. In this
	 * case the search for the next element of the list L1 must start from the
	 * position of the last element kept {@code syncNextIndex}.
	 */
	private Map<Integer, Integer> getCorrespondanceBetweenNextOrderAndPreviousOrder(CsmMix elementsFromPreviousOrder,
			CsmMix elementsFromNextOrder) {
		Map<Integer, Integer> correspondanceBetweenNextOrderAndPreviousOrder = new HashMap<>();
		ArrayIterator<CsmElement> previousOrderElementsIterator = new ArrayIterator<>(
				elementsFromPreviousOrder.getElements());
		int syncNextIndex = 0;
		while (previousOrderElementsIterator.hasNext()) {
			CsmElement pe = previousOrderElementsIterator.next();
			ArrayIterator<CsmElement> nextOrderElementsIterator = new ArrayIterator<>(
					elementsFromNextOrder.getElements(), syncNextIndex);
			while (nextOrderElementsIterator.hasNext()) {
				CsmElement ne = nextOrderElementsIterator.next();
				if (!correspondanceBetweenNextOrderAndPreviousOrder.values().contains(previousOrderElementsIterator.index())
						&& DifferenceElementCalculator.matching(ne, pe)) {
					correspondanceBetweenNextOrderAndPreviousOrder.put(nextOrderElementsIterator.index(),
							previousOrderElementsIterator.index());
					// set the position to start on the next {@code nextOrderElementsIterator} iteration
					syncNextIndex = nextOrderElementsIterator.index();
					break;
				}
			}
		}
		return correspondanceBetweenNextOrderAndPreviousOrder;
	}

	private List<Integer> findIndexOfCorrespondingNodeTextElement(List<CsmElement> elements, NodeText nodeText, int startIndex, Node node) {
        List<Integer> correspondingIndices = new ArrayList<>();
        for (ListIterator<CsmElement> csmElementListIterator = elements.listIterator(); csmElementListIterator.hasNext(); ) {
            int previousCsmElementIndex = csmElementListIterator.previousIndex();
            CsmElement csmElement = csmElementListIterator.next();
            int nextCsmElementIndex = csmElementListIterator.nextIndex();
            Map<MatchClassification, Integer> potentialMatches = new EnumMap<>(MatchClassification.class);
            for (int i = startIndex; i < nodeText.numberOfElements(); i++) {
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
                        if (i < nodeText.numberOfElements() - 1 && nextCsmElementIndex < elements.size()) {
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
            Optional<MatchClassification> bestMatchKey = potentialMatches.keySet().stream().min(Comparator.comparing(MatchClassification::getPriority));
            if (bestMatchKey.isPresent()) {
                correspondingIndices.add(potentialMatches.get(bestMatchKey.get()));
            } else {
                correspondingIndices.add(-1);
            }
        }
        return correspondingIndices;
    }

	private boolean isCorrespondingElement(TextElement textElement, CsmElement csmElement, Node node) {
        if (csmElement instanceof CsmToken) {
            CsmToken csmToken = (CsmToken) csmElement;
            if (textElement instanceof TokenTextElement) {
                TokenTextElement tokenTextElement = (TokenTextElement) textElement;
                return tokenTextElement.getTokenKind() == csmToken.getTokenType() && tokenTextElement.getText().equals(csmToken.getContent(node));
            }
        } else if (csmElement instanceof CsmChild) {
            CsmChild csmChild = (CsmChild) csmElement;
            if (textElement instanceof ChildTextElement) {
                ChildTextElement childTextElement = (ChildTextElement) textElement;
                return childTextElement.getChild() == csmChild.getChild();
            }
        } else if (csmElement instanceof CsmIndent) {
        	CsmIndent csmIndent = (CsmIndent) csmElement;
            if (textElement instanceof TokenTextElement) {
            	TokenTextElement tokenTextElement = (TokenTextElement) textElement;
                return tokenTextElement.isSpaceOrTab();
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
        return textElement.isWhiteSpace() && csmElement instanceof CsmToken && ((CsmToken) csmElement).isWhiteSpace();
    }
}
