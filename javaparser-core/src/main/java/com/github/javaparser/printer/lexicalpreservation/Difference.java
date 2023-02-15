/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.JavaToken;
import com.github.javaparser.JavaToken.Kind;
import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.IntStream;

import static com.github.javaparser.GeneratedJavaParserConstants.*;

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

    private final List<TextElement> indentation;

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

    /*
     * Returns the indentation used after the last line break
     */
    private List<TextElement> processIndentation(List<TextElement> indentation, List<TextElement> prevElements) {
        int eolIndex = lastIndexOfEol(prevElements);
        // Return "indentation" as is if no EOL element was found
        if (eolIndex < 0)
            return indentation;
        // Find consecutive space characters after the EOL element
        indentation = takeWhile(prevElements.subList(eolIndex + 1, prevElements.size()), element -> element.isWhiteSpace());
        return indentation;
    }
    
    /*
     * returns only the elements that match the given predicate.
     * takeWhile takes elements from the initial stream while the predicate holds true.
     * Meaning that when an element is encountered that does not match the predicate, the rest of the list is discarded. 
     */
    List<TextElement> takeWhile(List<TextElement> prevElements, Predicate<TextElement> predicate) {
    	List<TextElement> spaces = new ArrayList<>();
    	for (TextElement element : prevElements) {
    		if (predicate.test(element)) {
    			spaces.add(element);
                continue;
            }
            break;
    	}
    	return spaces;
    }
    
    
    int lastIndexOfEol(List<TextElement> source) {
        return IntStream.range(0, source.size())
                       .map(i -> source.size() - i - 1)
                       .filter(i -> source.get(i).isNewline())
                       .findFirst()
                       .orElse(-1);
    }

    /*
     * Returns the position of the next element in the list starting from @{code fromIndex} which is a comment (Ignoring spaces)
     * or -1 if it's not a comment.
     */
    private int posOfNextComment(int fromIndex, List<TextElement> elements) {
        if (!isValidIndex(fromIndex, elements))
            return -1;
        ReadOnlyListIterator<TextElement> iterator = new ReadOnlyListIterator(elements, fromIndex);
        // search for the next consecutive space characters
        while (iterator.hasNext()) {
            TextElement element = iterator.next();
            if (element.isSpaceOrTab()) {
                continue;
            }
            if (element.isComment()) {
            	return iterator.index();
            }
            break;
        }
        return -1;
    }
    
    /*
     * Returns true if the next element in the list (starting from @{code fromIndex}) is a comment
     */
    private boolean isFollowedByComment(int fromIndex, List<TextElement> elements) {
    	return posOfNextComment(fromIndex, elements) != -1;
    }
    
    /*
     * Removes all elements in the list starting from @{code fromIndex}) ending to @{code toIndex})
     */
    private void removeElements(int fromIndex, int toIndex, List<TextElement> elements) {
    	if (!(isValidIndex(fromIndex, elements) && isValidIndex(toIndex, elements) && fromIndex <= toIndex))
            return;
        ListIterator<TextElement> iterator = elements.listIterator(fromIndex);
        // removing elements
        int count = fromIndex;
        while (iterator.hasNext() && count <= toIndex) {
        	TextElement element = iterator.next();
            iterator.remove();
            count++;
        }
    }
    
    private boolean isValidIndex(int index, List<?> elements) {
    	return index >= 0 && index <= elements.size();
    }

    /*
     * Returns the position of the last new line character or -1 if there is no eol in the specified list of TextElement 
     */
    int lastIndexOfEolWithoutGPT(List<TextElement> source) {
        ListIterator listIterator = source.listIterator(source.size());
        int lastIndex = source.size() - 1;
        while (listIterator.hasPrevious()) {
            TextElement elem = (TextElement) listIterator.previous();
            if (elem.isNewline()) {
                return lastIndex;
            }
            lastIndex--;
        }
        return -1;
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
        if (nodeTextIndex > 0 && nodeText.getTextElement(nodeTextIndex - 1).isToken(LBRACE)) {
            return true;
        }
        if (nodeTextIndex > 0 && nodeText.getTextElement(nodeTextIndex - 1).isSpaceOrTab()) {
            return isAfterLBrace(nodeText, nodeTextIndex - 1);
        }
        return false;
    }

    /**
     * If we are at the beginning of a line, with just spaces or tabs before/after the position of the deleted element
     * we should force the space to be the same as the current indentation.
     * This method handles the following case if we remove the modifier {@code public} ([ ] is an indent character)
     * {@code 
     * [ ][ ]public[ ][ ][ ]void[ ]m{}
     * <-1-->      <---2--->
     * 1/ current indentation
     * 2/ these whitespaces must be removed
     * }
     * should produce
     * {@code 
     * [ ][ ]void[ ]m{} 
     * }
     */
    private int considerEnforcingIndentation(NodeText nodeText, int nodeTextIndex) {
        return considerIndentation(nodeText, nodeTextIndex, indentation.size());
    }
    
    private int considerRemovingIndentation(NodeText nodeText, int nodeTextIndex) {
        return considerIndentation(nodeText, nodeTextIndex, 0);
    }
    
    private int considerIndentation(NodeText nodeText, int nodeTextIndex, int numberOfCharactersToPreserve) {
        EnforcingIndentationContext enforcingIndentationContext = defineEnforcingIndentationContext(nodeText, nodeTextIndex);
        // the next position in the list (by default the current position)
        int res = nodeTextIndex;
        if (enforcingIndentationContext.extraCharacters > 0) {
        	int extraCharacters = enforcingIndentationContext.extraCharacters > numberOfCharactersToPreserve ? enforcingIndentationContext.extraCharacters - numberOfCharactersToPreserve : 0;
            res = removeExtraCharacters(nodeText, enforcingIndentationContext.start, extraCharacters);
            // The next position must take into account the indentation
            res = extraCharacters > 0 ? res + numberOfCharactersToPreserve : res;
        }
        if (res < 0) {
            throw new IllegalStateException();
        }
        return res;
    }
    
    private boolean isEnforcingIndentationActivable(RemovedGroup removedGroup) {
		return (diffIndex + 1 >= diffElements.size() || !(diffElements.get(diffIndex + 1).isAdded()))
				&& originalIndex < originalElements.size()
				&& !removedGroup.isACompleteLine();
	}

    private boolean isRemovingIndentationActivable(RemovedGroup removedGroup) {
		return (diffIndex + 1 >= diffElements.size() || !(diffElements.get(diffIndex + 1).isAdded())) 
				&& originalIndex < originalElements.size()
				&& removedGroup.isACompleteLine();
	}
    
    /*
     * This data structure class hold the starting position of the first whitespace char 
     * and the number of consecutive whitespace (or tab) characters
     */
    private class EnforcingIndentationContext {
    	int start;
    	int extraCharacters;
    	public EnforcingIndentationContext(int start) {
    		this.start=start;
    		this.extraCharacters=0;
    	}
    }

    /**
     * Remove excess white space after deleting element.
     * @param nodeText Contains a list of elements to analyze
     * @param nodeTextIndex Starting position in the input list
     * @return The current position in the list of the elements
     */
    private int removeExtraCharacters(NodeText nodeText, int nodeTextIndex, int extraCharacters) {
        int count = 0;
        while (nodeTextIndex >= 0 && nodeTextIndex < nodeText.numberOfElements() && count < extraCharacters) {
            nodeText.removeElement(nodeTextIndex);
            count++;
        }
        return nodeTextIndex;
    }

    /**
     * Starting at {@code nodeTextIndex} this method tries to determine how many contiguous spaces there are between 
     * the previous end of line and the next non whitespace (or tab) character
     * @param nodeText List of elements to analyze
     * @param nodeTextIndex Starting position in the input list
     * @return EnforcingIndentationContext Data structure that hold the starting position of the first whitespace char and
     * The number of consecutive whitespace (or tab) characters
     */
    private EnforcingIndentationContext defineEnforcingIndentationContext(NodeText nodeText, int startIndex) {
    	EnforcingIndentationContext ctx = new EnforcingIndentationContext(startIndex);
    	// compute space before startIndex value
		if (startIndex < nodeText.numberOfElements() && startIndex > 0) {
			// at this stage startIndex points to the first element before the deleted one
			for (int i = startIndex - 1; i >= 0 && i < nodeText.numberOfElements(); i--) {
				if (nodeText.getTextElement(i).isNewline()) {
					break;
				}
				if (!nodeText.getTextElement(i).isSpaceOrTab()) {
					ctx = new EnforcingIndentationContext(startIndex);
					break;
				}
				ctx.start = i;
				ctx.extraCharacters++;
			}
		}
		// compute space after the deleted element
		if (nodeText.getTextElement(startIndex).isSpaceOrTab()) {
			for (int i = startIndex; i >= 0 && i < nodeText.numberOfElements(); i++) {
				if (nodeText.getTextElement(i).isNewline()) {
					break;
				}
				if (!nodeText.getTextElement(i).isSpaceOrTab()) {
					break;
				}
				ctx.extraCharacters++;
			}
		}
        
        return ctx;
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
            if (!isLeftOverDiffElement && !isLeftOverOriginalElement) {
                DifferenceElement diffElement = diffElements.get(diffIndex);
                if (diffElement.isAdded()) {
                    applyAddedDiffElement((Added) diffElement);
                } else {
                    TextElement originalElement = originalElements.get(originalIndex);
                    boolean originalElementIsChild = originalElement instanceof ChildTextElement;
                    boolean originalElementIsToken = originalElement instanceof TokenTextElement;
                    if (diffElement.isKept()) {
                        applyKeptDiffElement((Kept) diffElement, originalElement, originalElementIsChild, originalElementIsToken);
                    } else if (diffElement.isRemoved()) {
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
                throw new UnsupportedOperationException("NodeText: " + nodeText + ". Difference: " + this + " " + originalElement);
            }
            isLeftOverElement = true;
        }
        return isLeftOverElement;
    }

    private boolean applyLeftOverDiffElements() {
        boolean isLeftOverElement = false;
        if (diffIndex < diffElements.size() && originalIndex >= originalElements.size()) {
            DifferenceElement diffElement = diffElements.get(diffIndex);
            if (diffElement.isKept()) {
                diffIndex++;
            } else if (diffElement.isAdded()) {
                Added addedElement = (Added) diffElement;
                nodeText.addElement(originalIndex, addedElement.toTextElement());
                originalIndex++;
                diffIndex++;
            } else {
                // let's forget this element
                diffIndex++;
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
                // we find the correspond OCE (Original CSM Element)
                // * we first add new elements that are marked to be added before OCE
                // * if OCE is marked to be present also in the "after" CSM we add a kept element,
                // otherwise we add a removed element
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
     * <br>
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
        for (RemovedGroup removedGroup : removedGroups) {
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
            if (diffElement.isRemoved()) {
                if (firstElement == null) {
                    firstElement = i;
                }
                removedElementsMap.computeIfAbsent(firstElement, key -> new ArrayList<>()).add((Removed) diffElement);
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
                // When we don't try to remove a complete line 
                // and removing the element is not the first action of a replacement (removal followed by addition)
                // (in the latter case we keep the indentation)
                // then we want to enforce the indentation.
                if (isEnforcingIndentationActivable(removedGroup)) {
                	// Since the element has been deleted we try to start the analysis from the element following the one that was deleted
                    originalIndex = considerEnforcingIndentation(nodeText, originalIndex);
                }
                // If in front we have one space and before also we had space let's drop one space
                if (originalElements.size() > originalIndex && originalIndex > 0) {
                    if (originalElements.get(originalIndex).isWhiteSpace() && originalElements.get(originalIndex - 1).isWhiteSpace()) {
                        // However we do not want to do that when we are about to adding or removing elements
                        // The intention is not very clear maybe it should clarify this with examples!
                        // Are we to understand that we can only do this if there is a single modification to process
                        // OR or if the next change is to keep the element
                        if ((diffIndex + 1) == diffElements.size() || (diffElements.get(diffIndex + 1).isKept())) {
                            originalElements.remove(originalIndex--);
                        }
                    }
                }
                // We need to know if, in the original list of elements, the deleted child node is immediately followed by the same comment.
                // If so, it should also be deleted.
                if (isFollowedByComment(originalIndex, originalElements) ) {
                	int indexOfNextComment = posOfNextComment(originalIndex, originalElements);
                	removeElements(originalIndex, indexOfNextComment, originalElements);
                }
                if (isRemovingIndentationActivable(removedGroup)) {
                	// Since the element has been deleted we try to start the analysis from the previous element
                    originalIndex = considerRemovingIndentation(nodeText, originalIndex);
                }
                diffIndex++;
            }
        } else if (removed.isChild() && originalElement.isComment()) {
        	// removing the comment first
        	nodeText.removeElement(originalIndex);
        	if (isRemovingIndentationActivable(removedGroup)) {
                originalIndex = considerRemovingIndentation(nodeText, originalIndex);
            }
        } else if (removed.isToken() && originalElementIsToken && (removed.getTokenType() == ((TokenTextElement) originalElement).getTokenKind() || // handle EOLs separately as their token kind might not be equal. This is because the 'removed'
        // element always has the current operating system's EOL as type
        (((TokenTextElement) originalElement).getToken().getCategory().isEndOfLine() && removed.isNewLine()))) {
            nodeText.removeElement(originalIndex);
            diffIndex++;
        } else if ((removed.isWhiteSpaceNotEol() || removed.getElement() instanceof CsmIndent || removed.getElement() instanceof CsmUnindent)
        		&& originalElement.isSpaceOrTab()){
        	// remove the current space
        	nodeText.removeElement(originalIndex);
        }else if (originalElementIsToken && originalElement.isWhiteSpaceOrComment()) {
            originalIndex++;
            // skip the newline token which may be generated unnecessarily by the concrete syntax pattern
            if (removed.isNewLine()) { 
            	diffIndex++;
            }
        } else if (originalElement.isLiteral()) {
            nodeText.removeElement(originalIndex);
            diffIndex++;
        } else if (removed.isPrimitiveType()) {
            if (originalElement.isPrimitive()) {
                nodeText.removeElement(originalIndex);
                diffIndex++;
            } else {
                throw new UnsupportedOperationException("removed " + removed.getElement() + " vs " + originalElement);
            }
        } else if (removed.isWhiteSpace() || removed.getElement() instanceof CsmIndent || removed.getElement() instanceof CsmUnindent) {
            diffIndex++;
        } else if (originalElement.isWhiteSpace()) {
            originalIndex++;
        } else if (removed.isChild()) {
            // see issue #3721 this case is linked for example to a change of type of variable declarator
            nodeText.removeElement(originalIndex);
            diffIndex++;
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
        // we dont want to remove the indentation if the last removed element is a newline
        // because in this case we are trying to remove the indentation of the next child element
        if (!removedGroup.isProcessed() 
        		&& removedGroup.isLastElement(removed) 
        		&& removedGroup.isACompleteLine()
        		&& !removed.isNewLine()) {
            Integer lastElementIndex = removedGroup.getLastElementIndex();
            Optional<Integer> indentation = removedGroup.getIndentation();
            if (indentation.isPresent() && !isReplaced(lastElementIndex)) {
                for (int i = 0; i < indentation.get(); i++) {
                    if (originalElements.get(originalIndex).isSpaceOrTab()) {
                        // If the current element is a space, remove it
                        nodeText.removeElement(originalIndex);
                    } else if (originalIndex >= 1 && originalElements.get(originalIndex - 1).isSpaceOrTab()) {
                        // If the current element is not a space itself we remove the space in front of (before) it
                        nodeText.removeElement(originalIndex - 1);
                        originalIndex--;
                    }
                    // Remove remaining newline character if needed
                    if (nodeText.getTextElement(originalIndex).isNewline()) {
                    	nodeText.removeElement(originalIndex);
                    	originalIndex = originalIndex > 0 ? originalIndex-- : 0;
                    }
                }
            }
            // Mark RemovedGroup as processed
            removedGroup.processed();
        }
    }

    // note:
    // increment originalIndex if we want to keep the original element
    // increment diffIndex if we want to skip the diff element
    private void applyKeptDiffElement(Kept kept, TextElement originalElement, boolean originalElementIsChild, boolean originalElementIsToken) {
		if (originalElement.isComment()) {
			originalIndex++;
        } else if (kept.isChild() && ((CsmChild) kept.getElement()).getChild() instanceof Comment) {
            diffIndex++;
        } else if (kept.isChild() && originalElementIsChild) {
            diffIndex++;
            originalIndex++;
        } else if (kept.isChild() && originalElementIsToken) {
            if (originalElement.isWhiteSpaceOrComment()) {
                originalIndex++;
            } else if (originalElement.isIdentifier() && isNodeWithTypeArguments(kept)) {
                diffIndex++;
                // skip all token related to node with type argument declaration
                // for example:
                // List i : in this case originalElement is "List" and the next token is space. There is nothing to skip. in the originalElements list.
                // List<String> i : in this case originalElement is "List" and the next token is
                // "<" so we have to skip all the tokens which are used in the typed argument declaration [<][String][>](3 tokens) in the originalElements list.
                // List<List<String>> i : in this case originalElement is "List" and the next
                // token is "<" so we have to skip all the tokens which are used in the typed arguments declaration [<][List][<][String][>][>](6 tokens) in the originalElements list.
                int step = getIndexToNextTokenElement((TokenTextElement) originalElement, 0);
                originalIndex += step;
                originalIndex++;
            } else if (originalElement.isIdentifier() && isTypeWithFullyQualifiedName(kept)) {
                diffIndex++;
                // skip all token related to node with the fully qualified name
                // for example:
                // java.lang.Object is represented in originalElement as a list of tokens "java", ".", "lang", ".", "Object".
                // So we have to skip 5 tokens.
                int step = getIndexToNextTokenElement((TokenTextElement) originalElement, kept);
                originalIndex += step;
                // positioning on the next token
                originalIndex++;
            } else if ((originalElement.isIdentifier() || originalElement.isKeyword()) && isArrayType(kept)) {
                int tokenToSkip = getIndexToNextTokenElementInArrayType((TokenTextElement) originalElement, getArrayLevel(kept));
                diffIndex++;
                originalIndex += tokenToSkip;
                originalIndex++;
            } else if (originalElement.isIdentifier()) {
                originalIndex++;
                diffIndex++;
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
            } else if (kept.isNewLine() && originalTextToken.isNewline()) {
                originalIndex++;
                diffIndex++;
            } else if (kept.isNewLine() && originalTextToken.isSpaceOrTab()) {
                originalIndex++;
            } else if (kept.isWhiteSpaceOrComment()) {
                diffIndex++;
            } else if (originalTextToken.isWhiteSpaceOrComment()) {
                originalIndex++;
            } else if (!kept.isNewLine() && originalTextToken.isSeparator()) {
                // case where originalTextToken is a separator like ";" and
                // kept is not a new line or whitespace for example "}"
                // see issue 2351
                originalIndex++;
            } else {
                throw new UnsupportedOperationException("Csm token " + kept.getElement() + " NodeText TOKEN " + originalTextToken);
            }
        } else if (kept.isToken() && originalElementIsChild) {
            diffIndex++;
        } else if (kept.isWhiteSpace()) {
            diffIndex++;
        } else if (kept.isIndent()) {
            diffIndex++;
        } else if (kept.isUnindent()) {
            // Nothing to do
            diffIndex++;
        } else {
            throw new UnsupportedOperationException("kept " + kept.getElement() + " vs " + originalElement);
        }
    }

    /*
     * Returns the array level if the DifferenceElement is a CsmChild representing an ArrayType else 0
     */
    private int getArrayLevel(DifferenceElement element) {
        CsmElement csmElem = element.getElement();
        if (isArrayType(element)) {
            Node child = ((LexicalDifferenceCalculator.CsmChild) csmElem).getChild();
            return ((ArrayType) child).getArrayLevel();
        }
        return 0;
    }

    /*
     * Returns true if the DifferenceElement is a CsmChild representing an ArrayType
     */
    private boolean isArrayType(DifferenceElement element) {
        CsmElement csmElem = element.getElement();
        return csmElem instanceof LexicalDifferenceCalculator.CsmChild && ((LexicalDifferenceCalculator.CsmChild) csmElem).getChild() instanceof ArrayType;
    }

    /*
     * Returns true if the DifferenceElement is a CsmChild which represents a type with fully qualified name
     */
    private boolean isTypeWithFullyQualifiedName(DifferenceElement element) {
        if (!element.isChild())
            return false;
        CsmChild child = (CsmChild) element.getElement();
        if (!ClassOrInterfaceType.class.isAssignableFrom(child.getChild().getClass()))
            return false;
        return ((ClassOrInterfaceType) child.getChild()).getScope().isPresent();
    }

    /*
     * Returns true if the DifferenceElement is a CsmChild with type arguments
     */
    private boolean isNodeWithTypeArguments(DifferenceElement element) {
        if (!element.isChild())
            return false;
        CsmChild child = (CsmChild) element.getElement();
        if (!NodeWithTypeArguments.class.isAssignableFrom(child.getChild().getClass()))
            return false;
        Optional<NodeList<Type>> typeArgs = ((NodeWithTypeArguments) child.getChild()).getTypeArguments();
        return typeArgs.isPresent() && typeArgs.get().size() > 0;
    }

    /*
     * Try to resolve the number of token to skip in the original list to match 
     * a ClassOrInterfaceType with a list of tokens like "java", ".", "lang", ".", "Object"
     */
    private int getIndexToNextTokenElement(TokenTextElement element, DifferenceElement kept) {
        // number of token to skip
        int step = 0;
        // verify if the DifferenceElement is a ClassOrInterfaceType with a fully qualified name
        if (!isTypeWithFullyQualifiedName(kept))
            return 0;
        CsmChild child = (CsmChild) kept.getElement();
        // split the type fully qualified node name to an array of tokens
        String[] parts = ((ClassOrInterfaceType) child.getChild()).getNameWithScope().split("\\.");
        JavaToken token = element.getToken();
        for (String part : parts) {
            if (part.equals(token.asString())) {
                // get 'dot' token
                token = token.getNextToken().get();
                if (!token.asString().equals("."))
                    break;
                // get the next part
                token = token.getNextToken().get();
                step += 2;
                continue;
            }
            // there is no match so we don't have token to skip
            step = 0;
            break;
        }
        return step;
    }

    /*
     * Returns the number of tokens to skip in originalElements list to synchronize it with the DiffElements list
     * This is due to the fact that types are considered as token in the originalElements list.
     * For example,
     * List<String> is represented by 4 tokens ([List][<][String][>]) while it's a CsmChild element in the DiffElements list
     * So in this case, getIndexToNextTokenElement(..) on the [List] token returns 3 because we have to skip 3 tokens ([<][String][>]) to synchronize
     * DiffElements list and originalElements list
     * The end of recursivity is reached when there is no next token or if the nested diamond operators are totally managed, to take into account this type of declaration
     * List <List<String>> l
     * Be careful, this method must be call only if diamond operator could be found in the sequence
     *
     * @Param TokenTextElement the token currently analyzed
     * @Param int the number of nested diamond operators
     * @return the number of token to skip in originalElements list
     */
    private int getIndexToNextTokenElement(TokenTextElement element, int nestedDiamondOperator) {
        // number of token to skip
        int step = 0;
        Optional<JavaToken> next = element.getToken().getNextToken();
        if (!next.isPresent())
            return step;
        // because there is a token, first we need to increment the number of token to skip
        step++;
        // manage nested diamond operators by incrementing the level on LT token and decrementing on GT
        JavaToken nextToken = next.get();
        Kind kind = Kind.valueOf(nextToken.getKind());
        if (isDiamondOperator(kind)) {
            if (kind.GT.equals(kind))
                nestedDiamondOperator--;
            else
                nestedDiamondOperator++;
        }
        // manage the fact where the first token is not a diamond operator but a whitespace
        // and the end of the token sequence to skip
        // for example in this declaration List <String> a;
        if (nestedDiamondOperator == 0 && !nextToken.getCategory().isWhitespace())
            return step;
        // recursively analyze token to skip
        return step += getIndexToNextTokenElement(new TokenTextElement(nextToken), nestedDiamondOperator);
    }

    /*
     * Returns the number of tokens to skip in originalElements list to synchronize it with the DiffElements list
     */
    private int getIndexToNextTokenElementInArrayType(TokenTextElement element, int arrayLevel) {
        // number of token to skip
        int step = 0;
        Optional<JavaToken> next = element.getToken().getNextToken();
        if (!next.isPresent())
            return step;
        // because there is a token, first we need to increment the number of token to skip
        step++;
        // manage array Level by decrementing the level on right bracket token
        JavaToken nextToken = next.get();
        Kind kind = Kind.valueOf(nextToken.getKind());
        if (isBracket(kind)) {
            if (kind.RBRACKET.equals(kind))
                arrayLevel--;
        }
        // manage the fact where the first token is not a diamond operator but a whitespace
        // and the end of the token sequence to skip
        // for example in this declaration int [] a;
        if (arrayLevel == 0 && !nextToken.getCategory().isWhitespace())
            return step;
        // recursively analyze token to skip
        return step += getIndexToNextTokenElementInArrayType(new TokenTextElement(nextToken), arrayLevel);
    }

    /*
     * Returns true if the token is possibly a diamond operator
     */
    private boolean isDiamondOperator(Kind kind) {
        return kind.GT.equals(kind) || kind.LT.equals(kind);
    }

    /*
     * Returns true if the token is a bracket
     */
    private boolean isBracket(Kind kind) {
        return kind.LBRACKET.equals(kind) || kind.RBRACKET.equals(kind);
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
        return nodeText.getTextElement(originalIndex).isToken(RBRACE) && doWeHaveLeftBraceFollowedBySpace(originalIndex - 1) && (diffIndex < 2 || !diffElements.get(diffIndex - 2).isRemoved());
    }

    private boolean doWeHaveLeftBraceFollowedBySpace(int index) {
        index = rewindSpace(index);
        return nodeText.getTextElement(index).isToken(LBRACE);
    }

    private int rewindSpace(int index) {
        if (index <= 0) {
            return index;
        }
        if (nodeText.getTextElement(index).isWhiteSpace()) {
            return rewindSpace(index - 1);
        } else {
            return index;
        }
    }

    private boolean nextIsRightBrace(int index) {
        List<TextElement> elements = originalElements.subList(index, originalElements.size());
        for (TextElement element : elements) {
            if (!element.isSpaceOrTab()) {
                return element.isToken(RBRACE);
            }
        }
        return false;
    }

    private void applyAddedDiffElement(Added added) {
        if (added.isIndent()) {
            for (int i = 0; i < STANDARD_INDENTATION_SIZE; i++) {
                indentation.add(new TokenTextElement(GeneratedJavaParserConstants.SPACE));
            }
            addedIndentation = true;
            diffIndex++;
            return;
        }
        if (added.isUnindent()) {
            for (int i = 0; i < STANDARD_INDENTATION_SIZE && !indentation.isEmpty(); i++) {
                indentation.remove(indentation.size() - 1);
            }
            addedIndentation = false;
            diffIndex++;
            return;
        }
        TextElement addedTextElement = added.toTextElement();
        boolean used = false;
        boolean isPreviousElementNewline = (originalIndex > 0) && originalElements.get(originalIndex - 1).isNewline();
        if (isPreviousElementNewline) {
            List<TextElement> elements = processIndentation(indentation, originalElements.subList(0, originalIndex - 1));
            boolean nextIsRightBrace = nextIsRightBrace(originalIndex);
            for (TextElement e : elements) {
                if (!nextIsRightBrace && e instanceof TokenTextElement && originalElements.get(originalIndex).isToken(((TokenTextElement) e).getTokenKind())) {
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
            boolean sufficientTokensRemainToSkip = nodeText.numberOfElements() > originalIndex + 2;
            boolean currentIsAComment = nodeText.getTextElement(originalIndex).isComment();
            boolean previousIsAComment = originalIndex > 0 && nodeText.getTextElement(originalIndex - 1).isComment();
            boolean currentIsNewline = nodeText.getTextElement(originalIndex).isNewline();
            boolean isFirstElement = originalIndex == 0;
            boolean previousIsWhiteSpace = originalIndex > 0 && nodeText.getTextElement(originalIndex - 1).isWhiteSpace();
			boolean commentIsBeforeAddedElement = currentIsAComment && addedTextElement.getRange().isPresent()
					&& nodeText.getTextElement(originalIndex).getRange()
							.map(range -> range.isBefore(addedTextElement.getRange().get())).orElse(false);
            if (sufficientTokensRemainToSkip && currentIsAComment && commentIsBeforeAddedElement) {
                // Need to get behind the comment:
                // FIXME: Why 2? This comment and the next newline?
                originalIndex += 2;
                // Defer originalIndex increment
                nodeText.addElement(originalIndex, addedTextElement);
                // We want to adjust the indentation while considering the new element that we added
                originalIndex = adjustIndentation(indentation, nodeText, originalIndex, false);
                // Now we can increment
                originalIndex++;
            } else if (currentIsNewline && previousIsAComment) {
                /*
                 * Manage the case where we want to add an element, after an expression which is followed by a comment on the same line.
                 * This is not the same case as the one who handles the trailing comments, because in this case the node text element is a new line (not a comment)
                 * For example : {@code private String a; // this is a }
                 */
                // Insert after the new line which follows this comment.
                originalIndex++;
                // We want to adjust the indentation while considering the new element that we added
                originalIndex = adjustIndentation(indentation, nodeText, originalIndex, false);
                // Defer originalIndex increment
                nodeText.addElement(originalIndex, addedTextElement);
                // Now we can increment.
                originalIndex++;
            } else if (currentIsNewline && addedTextElement.isChild()) {
                // here we want to place the new child element after the current new line character.
                // Except if indentation has been inserted just before this step (in the case where isPreviousElementNewline is true)
                // or if the previous character is a space (it could be the case if we want to replace a statement)
                // Example 1 : if we insert a statement (a duplicated method call expression ) after this one <code>  value();\n\n</code>
                // we want to have this result <code>  value();\n  value();\n</code> not <code>  value();\n  \nvalue();</code>
                // Example 2 : if we want to insert a statement after this one <code>  \n</code> we want to have <code>  value();\n</code>
                // not <code>  \nvalue();</code> --> this case appears on member replacement for example
                if (!isPreviousElementNewline && !isFirstElement && !previousIsWhiteSpace) {
                    // Insert after the new line
                    originalIndex++;
                }
                nodeText.addElement(originalIndex, addedTextElement);
                originalIndex++;
            } else {
                nodeText.addElement(originalIndex, addedTextElement);
                originalIndex++;
            }
        }
        if (addedTextElement.isNewline()) {
            boolean followedByUnindent = isFollowedByUnindent(diffElements, diffIndex);
            boolean nextIsRightBrace = nextIsRightBrace(originalIndex);
            boolean nextIsNewLine = originalElements.get(originalIndex).isNewline();
            if ((!nextIsNewLine && !nextIsRightBrace) || followedByUnindent) {
                originalIndex = adjustIndentation(indentation, nodeText, originalIndex, followedByUnindent);
            }
        }
        diffIndex++;
    }

    private String tokenDescription(int kind) {
        return GeneratedJavaParserConstants.tokenImage[kind];
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
		ReadOnlyListIterator<CsmElement> previousOrderElementsIterator = new ReadOnlyListIterator(
				elementsFromPreviousOrder.getElements());
		int syncNextIndex = 0;
		while (previousOrderElementsIterator.hasNext()) {
			CsmElement pe = previousOrderElementsIterator.next();
			ReadOnlyListIterator<CsmElement> nextOrderElementsIterator = new ReadOnlyListIterator(
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
    
    /*
     * A list iterator which does not allow to modify the list 
     * and which provides a method to know the current positioning 
     */
    private class ReadOnlyListIterator<T> implements ListIterator<T> {
    	ListIterator<T> elements;
    	public ReadOnlyListIterator(List<T> elements) {
    		this(elements, 0);
    	}
    	
    	public ReadOnlyListIterator(List<T> elements, int index) {
    		this.elements = elements.listIterator(index);
    	}

		@Override
		public boolean hasNext() {
			return elements.hasNext();
		}

		@Override
		public T next() {
			return elements.next();
		}

		@Override
		public boolean hasPrevious() {
			return elements.hasPrevious();
		}

		@Override
		public T previous() {
			return elements.previous();
		}

		@Override
		public int nextIndex() {
			return elements.nextIndex();
		}

		@Override
		public int previousIndex() {
			return elements.previousIndex();
		}
		
		/*
		 * Returns the current index in the underlying list
		 */
		public int index() {
			return elements.nextIndex() - 1;
		}
		
		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void set(T e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void add(T e) {
			throw new UnsupportedOperationException();
		}
    	
    }

    /*
     * Returns true if the next element in the list is an added element of type CsmUnindent
     */
    private boolean isFollowedByUnindent(List<DifferenceElement> diffElements, int diffIndex) {
        int nextIndexValue = diffIndex + 1;
        return (nextIndexValue) < diffElements.size() && diffElements.get(nextIndexValue).isAdded() && diffElements.get(nextIndexValue).getElement() instanceof CsmUnindent;
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

    private int adjustIndentation(List<TextElement> indentation, NodeText nodeText, int nodeTextIndex, boolean followedByUnindent) {
        List<TextElement> indentationAdj = processIndentation(indentation, nodeText.getElements().subList(0, nodeTextIndex - 1));
        if (nodeTextIndex < nodeText.numberOfElements() && nodeText.getTextElement(nodeTextIndex).isToken(RBRACE)) {
            indentationAdj = indentationAdj.subList(0, indentationAdj.size() - Math.min(STANDARD_INDENTATION_SIZE, indentationAdj.size()));
        } else if (followedByUnindent) {
            indentationAdj = indentationAdj.subList(0, Math.max(0, indentationAdj.size() - STANDARD_INDENTATION_SIZE));
        }
        for (TextElement e : indentationAdj) {
            if ((nodeTextIndex < nodeText.numberOfElements()) && nodeText.getTextElement(nodeTextIndex).isSpaceOrTab()) {
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

    /*
     * Returns true if the current <code>Added</code> element is preceded by a <code>Removed</code> element.
     */
    private boolean isAReplacement(int diffIndex) {
        return (diffIndex > 0) && diffElements.get(diffIndex).isAdded() && diffElements.get(diffIndex - 1).isRemoved();
    }

    /*
     * Returns true if the current <code>Removed</code> element is followed by a <code>Added</code> element.
     */
    private boolean isReplaced(int diffIndex) {
        return (diffIndex < diffElements.size() - 1) && diffElements.get(diffIndex + 1).isAdded() && diffElements.get(diffIndex).isRemoved();
    }

    @Override
    public String toString() {
        return "Difference{" + diffElements + '}';
    }
}
