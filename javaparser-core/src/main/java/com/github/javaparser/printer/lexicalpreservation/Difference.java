/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.concretesyntaxmodel.CsmUnindent;
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

    public static final int STANDARD_INDENTATION_SIZE = 4;

    private final NodeText nodeText;
    private final Node node;

    private final List<DifferenceElement> differenceElements;
    private final List<TextElement> textElements;
    private int indexOfTextElements = 0;
    private int indexOfDifferenceElements = 0;

    private final List<TokenTextElement> indentation;
    private boolean addedIndentation = false;

    Difference(List<DifferenceElement> differenceElements, NodeText nodeText, Node node) {
        if (nodeText == null) {
            throw new NullPointerException("nodeText can not be null");
        }

        this.nodeText = nodeText;
        this.node = node;
        this.differenceElements = differenceElements;
        this.textElements = nodeText.getElements();

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
        extractReshuffledDiffElements(differenceElements);
        Map<Removed, RemovedGroup> removedGroups = combineRemovedElementsToRemovedGroups();

        do {
            boolean isLeftOverDiffElement = applyLeftOverDiffElements();
            boolean isLeftOverOriginalElement = applyLeftOverOriginalElements();

            if (!isLeftOverDiffElement && !isLeftOverOriginalElement){
                DifferenceElement diffElement = differenceElements.get(indexOfDifferenceElements);

                if (diffElement instanceof Added) {
                    applyAddedDiffElement((Added) diffElement);
                } else {
                    TextElement originalElement = textElements.get(indexOfTextElements);
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
        } while (indexOfDifferenceElements < differenceElements.size() || indexOfTextElements < textElements.size());
    }

    private boolean applyLeftOverOriginalElements() {
        boolean isLeftOverElement = false;
        if (indexOfDifferenceElements >= differenceElements.size() && indexOfTextElements < textElements.size()) {
            TextElement originalElement = textElements.get(indexOfTextElements);

            if (originalElement.isWhiteSpaceOrComment()) {
                indexOfTextElements++;
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
        if (indexOfDifferenceElements < differenceElements.size() && indexOfTextElements >= textElements.size()) {
            DifferenceElement diffElement = differenceElements.get(indexOfDifferenceElements);
            if (diffElement instanceof Kept) {
                Kept kept = (Kept) diffElement;

                if (kept.isWhiteSpaceOrComment() || kept.isIndent() || kept.isUnindent()) {
                    indexOfDifferenceElements++;
                } else {
                    throw new IllegalStateException("Cannot keep element because we reached the end of nodetext: "
                            + nodeText + ". Difference: " + this);
                }
            } else if (diffElement instanceof Added) {
                Added addedElement = (Added) diffElement;

                nodeText.addElement(indexOfTextElements, addedElement.toTextElement());
                indexOfTextElements++;
                indexOfDifferenceElements++;
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
                boolean includeNewlineVariantsAsEqual = true;
                List<Integer> nodeTextIndexOfPreviousElements = findIndexOfCorrespondingNodeTextElement(elementsFromPreviousOrder.getElements(), nodeText, indexOfTextElements, node, includeNewlineVariantsAsEqual);

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
                    for (int ntIndex = indexOfTextElements; ntIndex <= lastNodeTextIndex; ntIndex++) {

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
        for (int i = 0; i < differenceElements.size(); i++) {
            DifferenceElement diffElement = differenceElements.get(i);
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
                    nodeText.removeElement(indexOfTextElements);
                } else {
                    indexOfTextElements++;
                }
            } else {
                nodeText.removeElement(indexOfTextElements);

                if ((indexOfDifferenceElements + 1 >= differenceElements.size() || !(differenceElements.get(indexOfDifferenceElements + 1) instanceof Added))
                        && !removedGroup.isACompleteLine()) {
                    indexOfTextElements = considerEnforcingIndentation(nodeText, indexOfTextElements);
                }
                // If in front we have one space and before also we had space let's drop one space
                if (textElements.size() > indexOfTextElements && indexOfTextElements > 0) {
                    if (textElements.get(indexOfTextElements).isWhiteSpace()
                            && textElements.get(indexOfTextElements - 1).isWhiteSpace()) {
                        // However we do not want to do that when we are about to adding or removing elements
                        if ((indexOfDifferenceElements + 1) == differenceElements.size() || (differenceElements.get(indexOfDifferenceElements + 1) instanceof Kept)) {
                            textElements.remove(indexOfTextElements--);
                        }
                    }
                }

                indexOfDifferenceElements++;
            }
        } else if (removed.isToken() && originalElementIsToken &&
                (removed.getTokenType() == ((TokenTextElement) originalElement).getTokenKind()
                        // handle EOLs separately as their token kind might not be equal. This is because the 'removed'
                        // element always has the current operating system's EOL as type
                        || (((TokenTextElement) originalElement).getToken().getCategory().isEndOfLine()
                                && removed.isNewLine()))) {
            nodeText.removeElement(indexOfTextElements);
            indexOfDifferenceElements++;
        } else if (originalElementIsToken && originalElement.isWhiteSpaceOrComment()) {
            indexOfTextElements++;
        } else if (originalElement.isLiteral()) {
            nodeText.removeElement(indexOfTextElements);
            indexOfDifferenceElements++;
        } else if (removed.isPrimitiveType()) {
            if (originalElement.isPrimitive()) {
                nodeText.removeElement(indexOfTextElements);
                indexOfDifferenceElements++;
            } else {
                throw new UnsupportedOperationException("removed " + removed.getElement() + " vs " + originalElement);
            }
        } else if (removed.isWhiteSpace() || removed.getElement() instanceof CsmIndent || removed.getElement() instanceof CsmUnindent) {
            indexOfDifferenceElements++;
        } else if (originalElement.isWhiteSpace()) {
            indexOfTextElements++;
        } else {
            throw new UnsupportedOperationException("removed " + removed.getElement() + " vs " + originalElement);
        }

        cleanTheLineOfLeftOverSpace(removedGroup, removed);
    }

    /**
     * Cleans the line of left over space if there is unnecessary indentation and the element will not be replaced
     */
    private void cleanTheLineOfLeftOverSpace(RemovedGroup removedGroup, Removed removed) {
        if (indexOfTextElements >= textElements.size()) {
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
                    if (textElements.get(indexOfTextElements).isSpaceOrTab()) {
                        // If the current element is a space, remove it
                        nodeText.removeElement(indexOfTextElements);
                    } else if (indexOfTextElements >= 1 && textElements.get(indexOfTextElements - 1).isSpaceOrTab()) {
                        // If the current element is not a space itself we remove the space in front of it
                        nodeText.removeElement(indexOfTextElements - 1);
                        indexOfTextElements--;
                    }
                }
            }

            // Mark RemovedGroup as processed
            removedGroup.processed();
        }
    }

    private void applyKeptDiffElement(Kept kept, TextElement originalElement, boolean originalElementIsChild, boolean originalElementIsToken) {
        if (originalElement.isComment()) {
            indexOfTextElements++;
        } else if (kept.isChild() && ((CsmChild)kept.getElement()).getChild() instanceof Comment ) {
            indexOfDifferenceElements++;
        } else if (kept.isChild() && originalElementIsChild) {
            indexOfDifferenceElements++;
            indexOfTextElements++;
        } else if (kept.isChild() && originalElementIsToken) {
            if (originalElement.isWhiteSpaceOrComment()) {
                indexOfTextElements++;
            } else if (originalElement.isIdentifier() && isNodeWithTypeArguments(kept)) {
                indexOfDifferenceElements++;
                // skip all token related to node with type argument declaration
                // for example:
                // List i : in this case originalElement is "List" and the next token is space. There is nothing to skip. in the originalElements list.
                // List<String> i : in this case originalElement is "List" and the next token is
                // "<" so we have to skip all the tokens which are used in the typed argument declaration [<][String][>](3 tokens) in the originalElements list.
                // List<List<String>> i : in this case originalElement is "List" and the next
                // token is "<" so we have to skip all the tokens which are used in the typed arguments declaration [<][List][<][String][>][>](6 tokens) in the originalElements list.
                int step = getIndexToNextTokenElement((TokenTextElement) originalElement, 0);
                indexOfTextElements += step;
                indexOfTextElements++;
            } else if (originalElement.isIdentifier()) {
                indexOfTextElements++;
                indexOfDifferenceElements++;
            } else {
                if (kept.isPrimitiveType()) {
                    indexOfTextElements++;
                    indexOfDifferenceElements++;
                } else {
                    throw new UnsupportedOperationException("kept " + kept.getElement() + " vs " + originalElement);
                }
            }
        } else if (kept.isToken() && originalElementIsToken) {
            TokenTextElement originalTextToken = (TokenTextElement) originalElement;

            if (kept.getTokenType() == originalTextToken.getTokenKind()) {
                indexOfTextElements++;
                indexOfDifferenceElements++;
            } else if (kept.isNewLine() && originalTextToken.isSpaceOrTab()) {
                indexOfTextElements++;
                indexOfDifferenceElements++;
             // case where originalTextToken is a separator like ";" and
             // kept is not a new line or whitespace for example "}"
             // see issue 2351
            }  else if (!kept.isNewLine() && originalTextToken.isSeparator()) {
                indexOfTextElements++;
            } else if (kept.isWhiteSpaceOrComment()) {
                indexOfDifferenceElements++;
            } else if (originalTextToken.isWhiteSpaceOrComment()) {
                indexOfTextElements++;
            } else {
                throw new UnsupportedOperationException("Csm token " + kept.getElement() + " NodeText TOKEN " + originalTextToken);
            }
        } else if (kept.isWhiteSpace()) {
            indexOfDifferenceElements++;
        } else if (kept.isIndent()) {
            indexOfDifferenceElements++;
        } else if (kept.isUnindent()) {
            // Nothing to do, beside considering indentation
            // However we want to consider the case in which the indentation was not applied, like when we have
            // just a left brace followed by space

            indexOfDifferenceElements++;
            if (!openBraceWasOnSameLine()) {
                for (int i = 0; i < STANDARD_INDENTATION_SIZE && indexOfTextElements >= 1 && nodeText.getTextElement(indexOfTextElements - 1).isSpaceOrTab(); i++) {
                    nodeText.removeElement(--indexOfTextElements);
                }
            }
        } else {
            throw new UnsupportedOperationException("kept " + kept.getElement() + " vs " + originalElement);
        }
    }

    /*
     * Returns true if the DifferenceElement is a CsmChild with type arguments
     */
    private boolean isNodeWithTypeArguments(DifferenceElement element) {
        CsmElement csmElem = element.getElement();
        if (!CsmChild.class.isAssignableFrom(csmElem.getClass()))
            return false;
        CsmChild child = (CsmChild) csmElem;
        if (!NodeWithTypeArguments.class.isAssignableFrom(child.getChild().getClass()))
            return false;
        Optional<NodeList<Type>> typeArgs = ((NodeWithTypeArguments) child.getChild()).getTypeArguments();
        return typeArgs.isPresent() && typeArgs.get().size() > 0;
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
        int step = 0; // number of token to skip
        Optional<JavaToken> next = element.getToken().getNextToken();
        if (!next.isPresent()) return step;
        // because there is a token, first we need to increment the number of token to skip 
        step++;
        // manage nested diamond operators by incrementing the level on LT token and decrementing on GT
        JavaToken token = next.get();
        Kind kind = Kind.valueOf(token.getKind());
        if (isDiamondOperator(kind)) {
            if (kind.GT.equals(kind))
                nestedDiamondOperator--;
            else
                nestedDiamondOperator++;
        }
        // manage the fact where the first token is not a diamond operator but a whitespace
        // and the end of the token sequence to skip
        // for example in this declaration List <String> a;
        if (nestedDiamondOperator == 0 && !next.get().getCategory().isWhitespace())
            return step;
        // recursively analyze token to skip
        return step += getIndexToNextTokenElement(new TokenTextElement(token), nestedDiamondOperator);
    }
    
    /*
     * Returns true if the token is possibly a diamond operator
     */
    private boolean isDiamondOperator(Kind kind) {
        return kind.GT.equals(kind) || kind.LT.equals(kind);
    }

    private boolean openBraceWasOnSameLine() {
        int index = indexOfTextElements;
        while (index >= 0 && !nodeText.getTextElement(index).isNewline()) {
            if (nodeText.getTextElement(index).isToken(LBRACE)) {
                return true;
            }
            index--;
        }
        return false;
    }

    private boolean wasSpaceBetweenBraces() {
        return nodeText.getTextElement(indexOfTextElements).isToken(RBRACE)
                && doWeHaveLeftBraceFollowedBySpace(indexOfTextElements - 1)
                && (indexOfDifferenceElements < 2 || !differenceElements.get(indexOfDifferenceElements - 2).isRemoved());
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
        List<TextElement> elements = textElements.subList(index, textElements.size());
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
            indexOfDifferenceElements++;
            return;
        }
        if (added.isUnindent()) {
            for (int i = 0; i<STANDARD_INDENTATION_SIZE && !indentation.isEmpty(); i++){
                indentation.remove(indentation.size() - 1);
            }
            addedIndentation = false;
            indexOfDifferenceElements++;
            return;
        }

        TextElement addedTextElement = added.toTextElement();
        boolean used = false;

        // FIRST FIGURE OUT THE INDENTATION LEVEL TO INSERT AT
        boolean isPreviousElementNewline = (indexOfTextElements > 0) && textElements.get(indexOfTextElements - 1).isNewline();
        if (isPreviousElementNewline) {
            List<TextElement> elements = processIndentation(indentation, textElements.subList(0, indexOfTextElements - 1));
            boolean nextIsRightBrace = nextIsRightBrace(indexOfTextElements);
            for (TextElement e : elements) {
                if (!nextIsRightBrace
                        && e instanceof TokenTextElement
                        && textElements.get(indexOfTextElements).isToken(((TokenTextElement)e).getTokenKind())) {
                    indexOfTextElements++;
                } else {
                    nodeText.addElement(indexOfTextElements++, e);
                }
            }
        } else if (isAfterLBrace(nodeText, indexOfTextElements) && !isAReplacement(indexOfDifferenceElements)) {
            if (addedTextElement.isNewline()) {
                used = true;
            }
            nodeText.addElement(indexOfTextElements++, new TokenTextElement(TokenTypes.eolTokenKind()));
            // This remove the space in "{ }" when adding a new line
            while (indexOfTextElements >= 2 && textElements.get(indexOfTextElements - 2).isSpaceOrTab()) {
                textElements.remove(indexOfTextElements - 2);
                indexOfTextElements--;
            }
            for (TextElement e : processIndentation(indentation, textElements.subList(0, indexOfTextElements - 1))) {
                nodeText.addElement(indexOfTextElements++, e);
            }
            // Indentation is painful...
            // Sometimes we want to force indentation: this is the case when indentation was expected but
            // was actually not there. For example if we have "{ }" we would expect indentation but it is
            // not there, so when adding new elements we force it. However if the indentation has been
            // inserted by us in this transformation we do not want to insert it again
            if (!addedIndentation) {
                for (TextElement e : indentationBlock()) {
                    nodeText.addElement(indexOfTextElements++, e);
                }
            }
        }

        if (!used) {
//            // FIXME: These extracted variables are buggy -- had to revert to the original conditions for tests to pass.
//            boolean sufficientTokensRemainToSkip = nodeText.numberOfElements() > originalIndex + 2;
//            boolean currentIsAComment = nodeText.getTextElement(originalIndex).isComment();
//            boolean previousIsAComment = originalIndex > 0 && nodeText.getTextElement(originalIndex - 1).isComment();
//            boolean currentIsNewline = nodeText.getTextElement(originalIndex).isNewline();

            TextElement currentTextElement = nodeText.getTextElement(indexOfTextElements);
            boolean currentElementIsNewline = currentTextElement.isNewline();
            boolean previousElementIsNewline = indexOfTextElements > 0 && nodeText.getTextElement(indexOfTextElements - 1).isNewline();
            boolean previousElementIsComment = indexOfTextElements > 0 && nodeText.getTextElement(indexOfTextElements - 1).isComment();
            boolean elementIsCommentFollowedByAnyElement = nodeText.numberOfElements() > indexOfTextElements + 1 && currentTextElement.isComment();

            if (!previousElementIsNewline && elementIsCommentFollowedByAnyElement) {
                // Handling trailing comments
                // Note that we need to get behind the comment and the newline that follows it (i.e. skip two elements):
                indexOfTextElements += 2;

                // Insert the added element
                nodeText.addElement(indexOfTextElements, addedTextElement); // NB: Defer originalIndex increment until indentation adjusted.

                // We want to adjust the indentation while considering the new element that we just added
                indexOfTextElements = adjustIndentation(indentation, nodeText, indexOfTextElements, false);
                indexOfTextElements++; // Now we can increment
            } else if (currentElementIsNewline && previousElementIsComment) {
                /*
                 * Manage the case where we want to add an element, after an expression which is followed by a comment on the same line.
                 * This is not the same case as the one who handles the trailing comments, because in this case the node text element is a new line (not a comment)
                 * For example : {@code private String a; // this is a }
                 */
                indexOfTextElements++; // Insert after the new line which follows this comment.

                // We want to adjust the indentation while considering the new element that we added
                indexOfTextElements = adjustIndentation(indentation, nodeText, indexOfTextElements, false);
                nodeText.addElement(indexOfTextElements, addedTextElement); // Defer originalIndex increment

                indexOfTextElements++; // Now we can increment.
            } else {
                nodeText.addElement(indexOfTextElements, addedTextElement);
                indexOfTextElements++;
            }
        }

        if (addedTextElement.isNewline()) {
            // We have already incremented the indices above,
            // therefore "next" refers to this already updated index.
            boolean followedByUnindent = isFollowedByUnindent(differenceElements, indexOfDifferenceElements);
            boolean nextIsRightBrace = nextIsRightBrace(indexOfTextElements);
            boolean nextIsNewLine = nodeText.getTextElement(indexOfTextElements).isNewline();
            if ((!nextIsNewLine && !nextIsRightBrace) || followedByUnindent) {
                indexOfTextElements = adjustIndentation(indentation, nodeText, indexOfTextElements, followedByUnindent);
            }
        }

        indexOfDifferenceElements++;
    }

    private String tokenDescription(int kind) {
        return GeneratedJavaParserConstants.tokenImage[kind];
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

    private List<Integer> findIndexOfCorrespondingNodeTextElement(List<CsmElement> elements, NodeText nodeText, int startIndex, Node node, boolean includeNewlineVariantsAsEqual) {
        List<Integer> correspondingIndices = new ArrayList<>();
        for (ListIterator<CsmElement> csmElementListIterator = elements.listIterator(); csmElementListIterator.hasNext(); ) {

            int previousCsmElementIndex = csmElementListIterator.previousIndex();
            CsmElement csmElement = csmElementListIterator.next();
            int nextCsmElementIndex = csmElementListIterator.nextIndex();

            Map<MatchClassification, Integer> potentialMatches = new EnumMap<>(MatchClassification.class);
            for (int i = startIndex; i < nodeText.getElements().size(); i++) {
                // Avoid overwriting a previously set link
                if (!correspondingIndices.contains(i)) {
                    TextElement textElement = nodeText.getTextElement(i);

                    boolean isCorresponding = isCorrespondingElement(textElement, csmElement, node, includeNewlineVariantsAsEqual);

                    if (isCorresponding) {
                        boolean hasSamePreviousElement = false;
                        if (i > 0 && previousCsmElementIndex > -1) {
                            TextElement previousTextElement = nodeText.getTextElement(i - 1);
                            hasSamePreviousElement = isCorrespondingElement(previousTextElement, elements.get(previousCsmElementIndex), node, includeNewlineVariantsAsEqual);
                        }

                        boolean hasSameNextElement = false;
                        if (i < nodeText.getElements().size() - 1 && nextCsmElementIndex < elements.size()) {
                            TextElement nextTextElement = nodeText.getTextElement(i + 1);
                            hasSameNextElement = isCorrespondingElement(nextTextElement, elements.get(nextCsmElementIndex), node, includeNewlineVariantsAsEqual);
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
                    } else if (!includeNewlineVariantsAsEqual && isAlmostCorrespondingNewline(textElement, csmElement, node)) {
                        // If we aren't treating newline variants as equal (e.g. \n \r), rank a separator difference higher than "ALMOST"
                        potentialMatches.putIfAbsent(MatchClassification.NEWLINE, i);
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


    private boolean isAlmostCorrespondingNewline(TextElement textElement, CsmElement csmElement, Node node) {
        if (isCorrespondingElement(textElement, csmElement, node, false)) {
            return false;
        }
        if (csmElement instanceof CsmToken) {
            CsmToken csmToken = (CsmToken) csmElement;
            if (textElement instanceof TokenTextElement) {
                TokenTextElement tokenTextElement = (TokenTextElement) textElement;
                boolean bothAreNewlines = tokenTextElement.getToken().getCategory().isEndOfLine() && ((CsmToken) csmElement).isNewLine();
            }
        }
        return textElement.isWhiteSpace() && csmElement instanceof CsmToken && ((CsmToken) csmElement).isWhiteSpace();
    }


    private enum MatchClassification {
        ALL(1),
        PREVIOUS_AND_SAME(2),
        NEXT_AND_SAME(3),
        SAME_ONLY(4),
        NEWLINE(5),
        ALMOST(6);

        private final int priority;

        MatchClassification(int priority) {
            this.priority = priority;
        }

        int getPriority() {
            return priority;
        }
    }

    private boolean isCorrespondingElement(TextElement textElement, CsmElement csmElement, Node node, boolean includeNewlineVariantsAsEqual) {
        if (csmElement instanceof CsmToken) {
            CsmToken csmToken = (CsmToken) csmElement;
            if (textElement instanceof TokenTextElement) {
                // handle EOLs separately as their token kind might not be equal. This is because the 'removed'
                // element always has the current operating system's EOL as type
                TokenTextElement tokenTextElement = (TokenTextElement) textElement;
                boolean tokensAreEqual = tokenTextElement.getTokenKind() == csmToken.getTokenType() && tokenTextElement.getText().equals(csmToken.getContent(node));
                boolean bothAreNewlines = tokenTextElement.getToken().getCategory().isEndOfLine() && ((CsmToken) csmElement).isNewLine();

                return tokensAreEqual || (includeNewlineVariantsAsEqual && bothAreNewlines);
            }
        } else if (csmElement instanceof CsmChild) {
            CsmChild csmChild = (CsmChild) csmElement;
            if (textElement instanceof ChildTextElement) {
                ChildTextElement childTextElement = (ChildTextElement) textElement;
                return childTextElement.getChild() == csmChild.getChild();
            }
        } else {
            throw new UnsupportedOperationException();
        }

        return false;
    }

    private boolean isAlmostCorrespondingElement(TextElement textElement, CsmElement csmElement, Node node) {
        if (isCorrespondingElement(textElement, csmElement, node, false)) {
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
        return (diffIndex > 0) && differenceElements.get(diffIndex) instanceof Added && differenceElements.get(diffIndex - 1) instanceof Removed;
    }

    private boolean isReplaced(int diffIndex) {
        return (diffIndex < differenceElements.size() - 1) && differenceElements.get(diffIndex + 1) instanceof Added && differenceElements.get(diffIndex) instanceof Removed;
    }

    @Override
    public String toString() {
        return "Difference{" + differenceElements + '}';
    }
}
