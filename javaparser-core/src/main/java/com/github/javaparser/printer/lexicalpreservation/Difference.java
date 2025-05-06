/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import static com.github.javaparser.GeneratedJavaParserConstants.LBRACE;
import static com.github.javaparser.GeneratedJavaParserConstants.RBRACE;
import static com.github.javaparser.GeneratedJavaParserConstants.SPACE;

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
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmUnindent;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.IntStream;

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
    List<TextElement> processIndentation(List<TextElement> indentation, List<TextElement> prevElements) {
        int eolIndex = lastIndexOfEol(prevElements);
        // Return "indentation" as is if no EOL element was found
        if (eolIndex < 0) return indentation;
        // Find consecutive space characters after the EOL element
        indentation =
                takeWhile(prevElements.subList(eolIndex + 1, prevElements.size()), element -> element.isWhiteSpace());
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
        if (!isValidIndex(fromIndex, elements)) return -1;
        ArrayIterator<TextElement> iterator = new ArrayIterator<>(elements, fromIndex);
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
        if (!(isValidIndex(fromIndex, elements) && isValidIndex(toIndex, elements) && fromIndex <= toIndex)) return;
        ListIterator<TextElement> iterator = elements.listIterator(fromIndex);
        // removing elements
        int count = fromIndex;
        while (iterator.hasNext() && count <= toIndex) {
            iterator.next();
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
        ListIterator<TextElement> listIterator = source.listIterator(source.size());
        int lastIndex = source.size() - 1;
        while (listIterator.hasPrevious()) {
            TextElement elem = listIterator.previous();
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
    int considerEnforcingIndentation(NodeText nodeText, int nodeTextIndex) {
        return considerIndentation(nodeText, nodeTextIndex, indentation.size());
    }

    private int considerRemovingIndentation(NodeText nodeText, int nodeTextIndex) {
        return considerIndentation(nodeText, nodeTextIndex, 0);
    }

    private int considerIndentation(NodeText nodeText, int nodeTextIndex, int numberOfCharactersToPreserve) {
        EnforcingIndentationContext enforcingIndentationContext =
                defineEnforcingIndentationContext(nodeText, nodeTextIndex);
        // the next position in the list (by default the current position)
        int res = nodeTextIndex;
        if (enforcingIndentationContext.extraCharacters > 0) {
            int extraCharacters = enforcingIndentationContext.extraCharacters > numberOfCharactersToPreserve
                    ? enforcingIndentationContext.extraCharacters - numberOfCharactersToPreserve
                    : 0;
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
        return (isLastElement(diffElements, diffIndex)
                        || !(nextDiffElement(diffElements, diffIndex).isAdded()))
                && originalIndex < originalElements.size()
                && !removedGroup.isACompleteLine();
    }

    private boolean isRemovingIndentationActivable(RemovedGroup removedGroup) {
        return (isLastElement(diffElements, diffIndex)
                        || !(nextDiffElement(diffElements, diffIndex).isAdded()))
                && originalIndex < originalElements.size()
                && removedGroup.isACompleteLine();
    }

    private boolean isLastElement(List<?> list, int index) {
        return index + 1 >= list.size();
    }

    private DifferenceElement nextDiffElement(List<DifferenceElement> list, int index) {
        return list.get(index + 1);
    }

    /*
     * This data structure class hold the starting position of the first whitespace char
     * and the number of consecutive whitespace (or tab) characters
     */
    private class EnforcingIndentationContext {

        int start;

        int extraCharacters;

        public EnforcingIndentationContext(int start) {
            this(start, 0);
        }

        public EnforcingIndentationContext(int start, int extraCharacters) {
            this.start = start;
            this.extraCharacters = extraCharacters;
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
                if (!isSpaceOrTabElement(nodeText, i)) {
                    ctx = new EnforcingIndentationContext(startIndex);
                    break;
                }
                ctx.start = i;
                ctx.extraCharacters++;
            }
        }
        // compute space after the deleted element
        if (startIndex < nodeText.numberOfElements() && isSpaceOrTabElement(nodeText, startIndex)) {
            //			int startingFromIndex = startIndex == 0 ? startIndex : startIndex + 1;
            for (int i = startIndex; i >= 0 && i < nodeText.numberOfElements(); i++) {
                if (nodeText.getTextElement(i).isNewline()) {
                    break;
                }
                if (!isSpaceOrTabElement(nodeText, i)) {
                    break;
                }
                ctx.extraCharacters++;
            }
        }
        return ctx;
    }

    /*
     * An element is considered inlined if, before the line break, there are nodes in the list of elements
     */
    private boolean isInlined(NodeText nodeText, int startIndex) {
        boolean inlined = false;
        if (startIndex < nodeText.numberOfElements() && startIndex >= 0) {
            // at this stage startIndex points to the first element before the deleted one
            for (int i = startIndex; i < nodeText.numberOfElements(); i++) {
                if (nodeText.getTextElement(i).isNewline()) {
                    break;
                }
                if (nodeText.getTextElement(i).isChild()) {
                    inlined = true;
                    break;
                }
            }
        }
        return inlined;
    }

    /*
     * Returns true if the indexed element is a space or a tab
     */
    private boolean isSpaceOrTabElement(NodeText nodeText, int i) {
        return nodeText.getTextElement(i).isSpaceOrTab();
    }

    /**
     * Node that we have calculate the Difference we can apply to a concrete NodeText, modifying it according
     * to the difference (adding and removing the elements provided).
     */
    void apply() {
        ReshuffledDiffElementExtractor.of(nodeText).extract(diffElements);
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
                        applyKeptDiffElement(
                                (Kept) diffElement, originalElement, originalElementIsChild, originalElementIsToken);
                    } else if (diffElement.isRemoved()) {
                        Removed removed = (Removed) diffElement;
                        applyRemovedDiffElement(
                                removedGroups.get(removed),
                                removed,
                                originalElement,
                                originalElementIsChild,
                                originalElementIsToken);
                    } else {
                        throw new UnsupportedOperationException("Unable to apply operations from "
                                + diffElement.getClass().getSimpleName() + " to "
                                + originalElement.getClass().getSimpleName());
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
                throw new UnsupportedOperationException(
                        "NodeText: " + nodeText + ". Difference: " + this + " " + originalElement);
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
                removedElementsMap
                        .computeIfAbsent(firstElement, key -> new ArrayList<>())
                        .add((Removed) diffElement);
            } else {
                firstElement = null;
            }
        }
        return removedElementsMap;
    }

    private void applyRemovedDiffElement(
            RemovedGroup removedGroup,
            Removed removed,
            TextElement originalElement,
            boolean originalElementIsChild,
            boolean originalElementIsToken) {
        if (removed.isChild() && originalElementIsChild) {
            ChildTextElement originalElementChild = (ChildTextElement) originalElement;
            if (originalElementChild.isComment()) {
                // We expected to remove a proper node but we found a comment in between.
                // If the comment is associated to the node we want to remove we remove it as well, otherwise we keep it
                Comment comment = (Comment) originalElementChild.getChild();
                if (!comment.isOrphan()
                        && comment.getCommentedNode().isPresent()
                        && comment.getCommentedNode().get().equals(removed.getChild())) {
                    nodeText.removeElement(originalIndex);
                } else {
                    originalIndex++;
                }
            } else {
                // If we delete the first element, it is possible that there is an indentation to be deleted which is
                // stored in the parent node.
                NodeText parentNodeText = new NodeText();
                List<TextElement> indentationTokens = new ArrayList<>();
                if (originalIndex == 0 && removed.getChild().getParentNode().isPresent()) {
                    Node startingNodeForFindingIndentation = removed.getChild();
                    Node parentNode = removed.getChild().getParentNode().get();
                    parentNodeText = LexicalPreservingPrinter.getOrCreateNodeText(parentNode);
                    // If we are trying to delete the first element of a node and that node is also the first element of
                    // the parent node, we need to look for the grandfather node which logically contains the
                    // indentation characters.
                    // This is the case, for example, when trying to delete an annotation positioned on a method
                    // declaration.
                    // The token corresponding to the annotation is the first element of the annotation node
                    // and it is also the first element of the parent node (MethodDeclaration),
                    // so the previous indentation is defined in the parent node of the method declaration.
                    if (!parentNodeText.getElements().isEmpty()
                            && parentNode.getParentNode().isPresent()
                            && parentNodeText.getTextElement(0).equals(nodeText.getTextElement(originalIndex))) {
                        startingNodeForFindingIndentation = parentNode;
                        parentNodeText = LexicalPreservingPrinter.getOrCreateNodeText(
                                parentNode.getParentNode().get());
                    }
                    indentationTokens = LexicalPreservingPrinter.findIndentation(startingNodeForFindingIndentation);
                }
                nodeText.removeElement(originalIndex);
                // When we don't try to remove a complete line
                // and removing the element is not the first action of a replacement (removal followed by addition)
                // (in the latter case we keep the indentation)
                // then we want to enforce the indentation.
                if (isEnforcingIndentationActivable(removedGroup)) {
                    // Since the element has been deleted we try to start the analysis from the element following the
                    // one that was deleted
                    originalIndex = considerEnforcingIndentation(nodeText, originalIndex);
                }
                // If in front we have one space and before also we had space let's drop one space
                if (originalElements.size() > originalIndex && originalIndex > 0) {
                    if (originalElements.get(originalIndex).isWhiteSpace()
                            && originalElements.get(originalIndex - 1).isWhiteSpace()) {
                        // However we do not want to do that when we are about to adding or removing elements
                        // The intention is not very clear maybe it should clarify this with examples!
                        // Are we to understand that we can only do this if there is a single modification to process
                        // OR or if the next change is to keep the element
                        if ((diffIndex + 1) == diffElements.size()
                                || (diffElements.get(diffIndex + 1).isKept())) {
                            originalElements.remove(originalIndex--);
                        }
                    }
                }
                // We need to know if, in the original list of elements, the deleted child node is immediately followed
                // by the same comment.
                // If so, it should also be deleted.
                if (isFollowedByComment(originalIndex, originalElements)) {
                    int indexOfNextComment = posOfNextComment(originalIndex, originalElements);
                    removeElements(originalIndex, indexOfNextComment, originalElements);
                }
                if (isRemovingIndentationActivable(removedGroup)) {
                    // Since the element has been deleted we try to start the analysis from the previous element
                    originalIndex = considerRemovingIndentation(nodeText, originalIndex);
                    // If we delete the first element, it is possible that there is an indentation
                    // to be deleted which is stored in the parent node.
                    // We don't want to remove indentation when the node to remove is not the only
                    // node in the line (if there are other nodes before the next character
                    // indicating the end of line).
                    // This is for example the case when we want to delete an annotation declared on
                    // the same line as a method declaration.
                    if (originalIndex == 0 && !indentationTokens.isEmpty() && !isInlined(nodeText, originalIndex)) {
                        for (TextElement indentationToken : indentationTokens) {
                            parentNodeText.removeElement(
                                    parentNodeText.findElement(indentationToken.and(indentationToken.matchByRange())));
                        }
                    }
                }
                diffIndex++;
            }
        } else if (removed.isChild() && originalElement.isComment()) {
            // removing the comment first
            nodeText.removeElement(originalIndex);
            if (isRemovingIndentationActivable(removedGroup)) {
                originalIndex = considerRemovingIndentation(nodeText, originalIndex);
            }
        } else if (removed.isToken()
                && originalElementIsToken
                && (removed.getTokenType() == ((TokenTextElement) originalElement).getTokenKind()
                        || // handle EOLs separately as their token kind might not be equal. This is because the
                        // 'removed'
                        // element always has the current operating system's EOL as type
                        (((TokenTextElement) originalElement)
                                        .getToken()
                                        .getCategory()
                                        .isEndOfLine()
                                && removed.isNewLine()))) {
            nodeText.removeElement(originalIndex);
            diffIndex++;
        } else if ((removed.isWhiteSpaceNotEol()
                        || removed.getElement() instanceof CsmIndent
                        || removed.getElement() instanceof CsmUnindent)
                && originalElement.isSpaceOrTab()) {
            // remove the current space
            nodeText.removeElement(originalIndex);
        } else if (originalElementIsToken && originalElement.isWhiteSpaceOrComment()) {
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
        } else if (removed.isWhiteSpace()
                || removed.getElement() instanceof CsmIndent
                || removed.getElement() instanceof CsmUnindent) {
            diffIndex++;
        } else if (originalElement.isWhiteSpace()) {
            originalIndex++;
        } else if (removed.isChild()) {
            // see issue #3721 this case is linked for example to a change of type of variable declarator
            nodeText.removeElement(originalIndex);
            diffIndex++;
        } else if (originalElement.isChild() && removed.isToken()) {
            // see issue #4747 this case is linked for example to a change of the annotation name
            // This happens because changing a name results in the creation of a token when the syntax of the modified
            // node is evaluated, whereas parsing an annotation results in a representation containing a child node
            // (representing the annotation name). When the annotation name is modified, the element to be deleted (the
            // child node) is compared with the token containing the character string representing the new annotation
            // name.
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
                    } else if (originalIndex >= 1
                            && originalElements.get(originalIndex - 1).isSpaceOrTab()) {
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
    private void applyKeptDiffElement(
            Kept kept, TextElement originalElement, boolean originalElementIsChild, boolean originalElementIsToken) {
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
                // List i : in this case originalElement is "List" and the next token is space. There is nothing to
                // skip. in the originalElements list.
                // List<String> i : in this case originalElement is "List" and the next token is
                // "<" so we have to skip all the tokens which are used in the typed argument declaration
                // [<][String][>](3 tokens) in the originalElements list.
                // List<List<String>> i : in this case originalElement is "List" and the next
                // token is "<" so we have to skip all the tokens which are used in the typed arguments declaration
                // [<][List][<][String][>][>](6 tokens) in the originalElements list.
                int step = getIndexToNextTokenElement((TokenTextElement) originalElement, 0);
                originalIndex += step;
                originalIndex++;
            } else if (originalElement.isIdentifier() && isTypeWithFullyQualifiedName(kept)) {
                diffIndex++;
                // skip all token related to node with the fully qualified name
                // for example:
                // java.lang.Object is represented in originalElement as a list of tokens "java", ".", "lang", ".",
                // "Object".
                // So we have to skip 5 tokens.
                int step = getIndexToNextTokenElement((TokenTextElement) originalElement, kept);
                originalIndex += step;
                // positioning on the next token
                originalIndex++;
            } else if ((originalElement.isIdentifier() || originalElement.isKeyword()) && isArrayType(kept)) {
                int tokenToSkip =
                        getIndexToNextTokenElementInArrayType((TokenTextElement) originalElement, getArrayLevel(kept));
                diffIndex++;
                originalIndex += tokenToSkip;
                originalIndex++;
            } else if (originalElement.isIdentifier()) {
                originalIndex++;
                diffIndex++;
            } else if (kept.isPrimitiveType()) {
                originalIndex++;
                diffIndex++;
            } else {
                // original is a token so we keep it (for example an unexpected semicolon)
                originalIndex++;
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
                throw new UnsupportedOperationException(
                        "Csm token " + kept.getElement() + " NodeText TOKEN " + originalTextToken);
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
        return csmElem instanceof LexicalDifferenceCalculator.CsmChild
                && ((LexicalDifferenceCalculator.CsmChild) csmElem).getChild() instanceof ArrayType;
    }

    /*
     * Returns true if the DifferenceElement is a CsmChild which represents a type with fully qualified name
     */
    private boolean isTypeWithFullyQualifiedName(DifferenceElement element) {
        if (!element.isChild()) return false;
        CsmChild child = (CsmChild) element.getElement();
        if (!ClassOrInterfaceType.class.isAssignableFrom(child.getChild().getClass())) return false;
        return ((ClassOrInterfaceType) child.getChild()).getScope().isPresent();
    }

    /*
     * Returns true if the DifferenceElement is a CsmChild with type arguments
     */
    private boolean isNodeWithTypeArguments(DifferenceElement element) {
        if (!element.isChild()) return false;
        CsmChild child = (CsmChild) element.getElement();
        if (!NodeWithTypeArguments.class.isAssignableFrom(child.getChild().getClass())) return false;
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
        if (!isTypeWithFullyQualifiedName(kept)) return 0;
        CsmChild child = (CsmChild) kept.getElement();
        // split the type fully qualified node name to an array of tokens
        String[] parts =
                ((ClassOrInterfaceType) child.getChild()).getNameWithScope().split("\\.");
        JavaToken token = element.getToken();
        for (String part : parts) {
            if (part.equals(token.asString())) {
                // get 'dot' token
                token = token.getNextToken().get();
                if (!".".equals(token.asString())) break;
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
        if (!next.isPresent()) return step;
        // because there is a token, first we need to increment the number of token to skip
        step++;
        // manage nested diamond operators by incrementing the level on LT token and decrementing on GT
        JavaToken nextToken = next.get();
        Kind kind = Kind.valueOf(nextToken.getKind());
        if (isDiamondOperator(kind)) {
            if (Kind.GT.equals(kind)) nestedDiamondOperator--;
            else nestedDiamondOperator++;
        }
        // manage the fact where the first token is not a diamond operator but a whitespace
        // and the end of the token sequence to skip
        // for example in this declaration List <String> a;
        if (nestedDiamondOperator == 0 && !nextToken.getCategory().isWhitespace()) return step;
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
        if (!next.isPresent()) return step;
        // because there is a token, first we need to increment the number of token to skip
        step++;
        // manage array Level by decrementing the level on right bracket token
        JavaToken nextToken = next.get();
        Kind kind = Kind.valueOf(nextToken.getKind());
        if (isBracket(kind)) {
            if (Kind.RBRACKET.equals(kind)) arrayLevel--;
        }
        // manage the fact where the first token is not a diamond operator but a whitespace
        // and the end of the token sequence to skip
        // for example in this declaration int [] a;
        if (arrayLevel == 0 && !nextToken.getCategory().isWhitespace()) return step;
        // recursively analyze token to skip
        return step += getIndexToNextTokenElementInArrayType(new TokenTextElement(nextToken), arrayLevel);
    }

    /*
     * Returns true if the token is possibly a diamond operator
     */
    private boolean isDiamondOperator(Kind kind) {
        return Kind.GT.equals(kind) || Kind.LT.equals(kind);
    }

    /*
     * Returns true if the token is a bracket
     */
    private boolean isBracket(Kind kind) {
        return Kind.LBRACKET.equals(kind) || Kind.RBRACKET.equals(kind);
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
        boolean isPreviousElementNewline =
                (originalIndex > 0) && originalElements.get(originalIndex - 1).isNewline();
        if (isPreviousElementNewline) {
            List<TextElement> elements =
                    processIndentation(indentation, originalElements.subList(0, originalIndex - 1));
            boolean nextIsRightBrace = nextIsRightBrace(originalIndex);
            for (TextElement e : elements) {
                if (!nextIsRightBrace
                        && e instanceof TokenTextElement
                        && originalElements.get(originalIndex).isToken(((TokenTextElement) e).getTokenKind())) {
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
            boolean previousIsAComment = originalIndex > 0
                    && nodeText.getTextElement(originalIndex - 1).isComment();
            boolean currentIsNewline = nodeText.getTextElement(originalIndex).isNewline();
            boolean isFirstElement = originalIndex == 0;
            boolean previousIsWhiteSpace = originalIndex > 0
                    && nodeText.getTextElement(originalIndex - 1).isWhiteSpace();
            boolean commentIsBeforeAddedElement = currentIsAComment
                    && addedTextElement.getRange().isPresent()
                    && nodeText.getTextElement(originalIndex)
                            .getRange()
                            .map(range ->
                                    range.isBefore(addedTextElement.getRange().get()))
                            .orElse(false);
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
                // Except if indentation has been inserted just before this step (in the case where
                // isPreviousElementNewline is true)
                // or if the previous character is a space (it could be the case if we want to replace a statement)
                // Example 1 : if we insert a statement (a duplicated method call expression ) after this one <code>
                // value();\n\n</code>
                // we want to have this result <code>  value();\n  value();\n</code> not <code>  value();\n
                // \nvalue();</code>
                // Example 2 : if we want to insert a statement after this one <code>  \n</code> we want to have <code>
                // value();\n</code>
                // not <code>  \nvalue();</code> --> this case appears on member replacement for example
                if (!isPreviousElementNewline && !isFirstElement && !previousIsWhiteSpace) {
                    // Insert after the new line
                    originalIndex++;
                    // We want to adjust the indentation while considering the new element that we
                    // added
                    originalIndex = adjustIndentation(indentation, nodeText, originalIndex, false);
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

    /*
     * A list iterator which provides a method to know the current positioning
     */
    public static class ArrayIterator<T> implements ListIterator<T> {

        ListIterator<T> iterator;

        public ArrayIterator(List<T> elements) {
            this(elements, 0);
        }

        public ArrayIterator(List<T> elements, int index) {
            this.iterator = elements.listIterator(index);
        }

        @Override
        public boolean hasNext() {
            return iterator.hasNext();
        }

        @Override
        public T next() {
            return iterator.next();
        }

        @Override
        public boolean hasPrevious() {
            return iterator.hasPrevious();
        }

        @Override
        public T previous() {
            return iterator.previous();
        }

        @Override
        public int nextIndex() {
            return iterator.nextIndex();
        }

        @Override
        public int previousIndex() {
            return iterator.previousIndex();
        }

        /*
         * Returns the current index in the underlying list
         */
        public int index() {
            return iterator.nextIndex() - 1;
        }

        @Override
        public void remove() {
            iterator.remove();
            ;
        }

        @Override
        public void set(T e) {
            iterator.set(e);
        }

        @Override
        public void add(T e) {
            iterator.add(e);
            ;
        }
    }

    /*
     * Returns true if the next element in the list is an added element of type CsmUnindent
     */
    private boolean isFollowedByUnindent(List<DifferenceElement> diffElements, int diffIndex) {
        int nextIndexValue = diffIndex + 1;
        return (nextIndexValue) < diffElements.size()
                && diffElements.get(nextIndexValue).isAdded()
                && diffElements.get(nextIndexValue).getElement() instanceof CsmUnindent;
    }

    private int adjustIndentation(
            List<TextElement> indentation, NodeText nodeText, int nodeTextIndex, boolean followedByUnindent) {
        List<TextElement> indentationAdj =
                processIndentation(indentation, nodeText.getElements().subList(0, nodeTextIndex - 1));
        if (nodeTextIndex < nodeText.numberOfElements()
                && nodeText.getTextElement(nodeTextIndex).isToken(RBRACE)) {
            indentationAdj = indentationAdj.subList(
                    0, indentationAdj.size() - Math.min(STANDARD_INDENTATION_SIZE, indentationAdj.size()));
        } else if (followedByUnindent) {
            indentationAdj = indentationAdj.subList(0, Math.max(0, indentationAdj.size() - STANDARD_INDENTATION_SIZE));
        }
        for (TextElement e : indentationAdj) {
            if ((nodeTextIndex < nodeText.numberOfElements())
                    && nodeText.getTextElement(nodeTextIndex).isSpaceOrTab()) {
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
        return (diffIndex > 0)
                && diffElements.get(diffIndex).isAdded()
                && diffElements.get(diffIndex - 1).isRemoved();
    }

    /*
     * Returns true if the current <code>Removed</code> element is followed by a <code>Added</code> element.
     */
    private boolean isReplaced(int diffIndex) {
        return (diffIndex < diffElements.size() - 1)
                && diffElements.get(diffIndex + 1).isAdded()
                && diffElements.get(diffIndex).isRemoved();
    }

    @Override
    public String toString() {
        return "Difference{" + diffElements + '}';
    }
}
