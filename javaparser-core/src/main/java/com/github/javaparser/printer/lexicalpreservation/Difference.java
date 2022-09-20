/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

import java.util.*;

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

    /*
     * Returns the indentation used after the last line break
     */
    private List<TextElement> processIndentation(List<TokenTextElement> indentation, List<TextElement> prevElements) {
        List<TextElement> res = new LinkedList<>(indentation);
        int index = lastIndexOfEol(prevElements);
        if (index < 0) return res; // no EOL found
        res.clear(); // initialize previous indentation
        // search for consecutive space characters
        for (int i = (index + 1); i < prevElements.size(); i++) {
            TextElement elem = prevElements.get(i);
            if (elem.isWhiteSpace()) {
                res.add(elem);
                continue;
            }
            break;
        }
        return res;
    }
    
    /*
     * Returns the position of the last new line character or -1 if there is no eol in the specified list of TextElement 
     */
    int lastIndexOfEol(List<TextElement> source) {
        ListIterator listIterator = source.listIterator(source.size());
        int lastIndex = source.size() -1;
        while (listIterator.hasPrevious()) {
            TextElement elem = (TextElement)listIterator.previous();
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
     * If we are at the beginning of a line, with just spaces or tabs before us we should force the space to be
     * the same as the indentation.
     */
    private int considerEnforcingIndentation(NodeText nodeText, int nodeTextIndex) {
        boolean hasOnlyWsBefore = true;
        for (int i = nodeTextIndex; i >= 0 && hasOnlyWsBefore && i < nodeText.numberOfElements(); i--) {
            if (nodeText.getTextElement(i).isNewline()) {
                break;
            }
            if (!nodeText.getTextElement(i).isSpaceOrTab()) {
                hasOnlyWsBefore = false;
            }
        }
        int res = nodeTextIndex;
        if (hasOnlyWsBefore) {
            for (int i = nodeTextIndex; i >= 0 && i < nodeText.numberOfElements(); i--) {
                if (nodeText.getTextElement(i).isNewline()) {
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
        for (int i = 0; i < diffElements.size(); i++) {
            DifferenceElement diffElement = diffElements.get(i);
            if (diffElement.isRemoved()) {
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

                if ((diffIndex + 1 >= diffElements.size() || !(diffElements.get(diffIndex + 1).isAdded()))
                        && !removedGroup.isACompleteLine()) {
                    originalIndex = considerEnforcingIndentation(nodeText, originalIndex);
                }
                // If in front we have one space and before also we had space let's drop one space
                if (originalElements.size() > originalIndex && originalIndex > 0) {
                    if (originalElements.get(originalIndex).isWhiteSpace()
                            && originalElements.get(originalIndex - 1).isWhiteSpace()) {
                        // However we do not want to do that when we are about to adding or removing elements
                        if ((diffIndex + 1) == diffElements.size() || (diffElements.get(diffIndex + 1).isKept())) {
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

    // note:
    // increment originalIndex if we want to keep the original element
    // increment diffIndex if we don't want to skip the diff element
    private void applyKeptDiffElement(Kept kept, TextElement originalElement, boolean originalElementIsChild, boolean originalElementIsToken) {
        if (originalElement.isComment()) {
            originalIndex++;
        } else if (kept.isChild() && ((CsmChild)kept.getElement()).getChild() instanceof Comment ) {
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
            }  else if (originalElement.isIdentifier() && isTypeWithFullyQualifiedName(kept)) {
                    diffIndex++;
                    // skip all token related to node with the fully qualified name
                    // for example:
                    // java.lang.Object is represented in originalElement as a list of tokens "java", ".", "lang", ".", "Object".
                    // So we have to skip 5 tokens.
                    int step = getIndexToNextTokenElement((TokenTextElement) originalElement, kept);
                    originalIndex += step;
                    originalIndex++; // positioning on the next token
            } else if ((originalElement.isIdentifier() || originalElement.isKeyword()) && isArrayType(kept)) {
                int tokenToSkip = getIndexToNextTokenElementInArrayType((TokenTextElement)originalElement, getArrayLevel(kept));
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
                diffIndex++;
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
        if (csmElem instanceof LexicalDifferenceCalculator.CsmChild &&
                ((LexicalDifferenceCalculator.CsmChild) csmElem).getChild() instanceof ArrayType) {
            Node child = ((LexicalDifferenceCalculator.CsmChild) csmElem).getChild();
            return ((ArrayType)child).getArrayLevel();
        }
        return 0;
    }

    /*
     * Returns true if the DifferenceElement is a CsmChild representing an ArrayType
     */
    private boolean isArrayType(DifferenceElement element) {
        CsmElement csmElem = element.getElement();
        return csmElem instanceof LexicalDifferenceCalculator.CsmChild &&
                ((LexicalDifferenceCalculator.CsmChild) csmElem).getChild() instanceof ArrayType;
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
        int step = 0; // number of token to skip
        if (!isTypeWithFullyQualifiedName(kept)) return 0; // verify if the DifferenceElement is a ClassOrInterfaceType with a fully qualified name
        CsmChild child = (CsmChild) kept.getElement();
        // split the type fully qualified node name to an array of tokens
        String[] parts = ((ClassOrInterfaceType) child.getChild()).getNameWithScope().split("\\.");
        JavaToken token = element.getToken();
        for (String part : parts) {
            if (part.equals(token.asString())) {
                token = token.getNextToken().get(); // get 'dot' token
                if (!token.asString().equals(".")) break;
                token = token.getNextToken().get(); // get the next part
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
        int step = 0; // number of token to skip
        Optional<JavaToken> next = element.getToken().getNextToken();
        if (!next.isPresent()) return step;
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
        int step = 0; // number of token to skip
        Optional<JavaToken> next = element.getToken().getNextToken();
        if (!next.isPresent()) return step;
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
        return nodeText.getTextElement(originalIndex).isToken(RBRACE)
                && doWeHaveLeftBraceFollowedBySpace(originalIndex - 1)
                && (diffIndex < 2 || !diffElements.get(diffIndex - 2).isRemoved());
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
        boolean isPreviousElementNewline = (originalIndex > 0) && originalElements.get(originalIndex - 1).isNewline();
        if (isPreviousElementNewline) {
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
            boolean sufficientTokensRemainToSkip = nodeText.numberOfElements() > originalIndex + 2;
            boolean currentIsAComment = nodeText.getTextElement(originalIndex).isComment();
            boolean previousIsAComment = originalIndex > 0 && nodeText.getTextElement(originalIndex - 1).isComment();
            boolean currentIsNewline = nodeText.getTextElement(originalIndex).isNewline();
            boolean isFirstElement = originalIndex == 0;
            boolean previousIsWhiteSpace = originalIndex > 0 && nodeText.getTextElement(originalIndex - 1).isWhiteSpace();

            if (sufficientTokensRemainToSkip && currentIsAComment) {
                // Need to get behind the comment:
                originalIndex += 2; // FIXME: Why 2? This comment and the next newline?
                nodeText.addElement(originalIndex, addedTextElement); // Defer originalIndex increment

                // We want to adjust the indentation while considering the new element that we added
                originalIndex = adjustIndentation(indentation, nodeText, originalIndex, false);
                originalIndex++; // Now we can increment
            } else if (currentIsNewline && previousIsAComment) {
                /*
                 * Manage the case where we want to add an element, after an expression which is followed by a comment on the same line.
                 * This is not the same case as the one who handles the trailing comments, because in this case the node text element is a new line (not a comment)
                 * For example : {@code private String a; // this is a }
                 */
                originalIndex++; // Insert after the new line which follows this comment.

                // We want to adjust the indentation while considering the new element that we added
                originalIndex = adjustIndentation(indentation, nodeText, originalIndex, false);
                nodeText.addElement(originalIndex, addedTextElement); // Defer originalIndex increment
                originalIndex++; // Now we can increment.
            } else if (currentIsNewline && addedTextElement.isChild()) {
                // here we want to place the new child element after the current new line character.
                // Except if indentation has been inserted just before this step (in the case where isPreviousElementNewline is true) 
                // or if the previous character is a space (it could be the case if we want to replace a statement)
                // Example 1 : if we insert a statement (a duplicated method call expression ) after this one <code>  value();\n\n</code>
                // we want to have this result <code>  value();\n  value();\n</code> not <code>  value();\n  \nvalue();</code>
                // Example 2 : if we want to insert a statement after this one <code>  \n</code> we want to have <code>  value();\n</code> 
                // not <code>  \nvalue();</code> --> this case appears on member replacement for example 
                if (!isPreviousElementNewline && !isFirstElement && !previousIsWhiteSpace) {
                    originalIndex++; // Insert after the new line
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
            boolean nextIsNewLine = nodeText.getTextElement(originalIndex).isNewline();
            if ((!nextIsNewLine && !nextIsRightBrace) || followedByUnindent) {
                originalIndex = adjustIndentation(indentation, nodeText, originalIndex, followedByUnindent);
            }
        }

        diffIndex++;
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

    /*
     * Returns true if the next element in the list is an added element of type CsmUnindent
     */
    private boolean isFollowedByUnindent(List<DifferenceElement> diffElements, int diffIndex) {
        int nextIndexValue = diffIndex + 1;
        return (nextIndexValue) < diffElements.size()
                && diffElements.get(nextIndexValue).isAdded()
                && diffElements.get(nextIndexValue).getElement() instanceof CsmUnindent;
    }

    private List<Integer> findIndexOfCorrespondingNodeTextElement(List<CsmElement> elements, NodeText nodeText, int startIndex, Node node) {
        List<Integer> correspondingIndices = new ArrayList<>();
        for (ListIterator<CsmElement> csmElementListIterator = elements.listIterator(); csmElementListIterator.hasNext(); ) {

            int previousCsmElementIndex = csmElementListIterator.previousIndex();
            CsmElement csmElement = csmElementListIterator.next();
            int nextCsmElementIndex = csmElementListIterator.nextIndex();

            Map<MatchClassification, Integer> potentialMatches = new EnumMap<>(MatchClassification.class);
            for (int i = startIndex; i < nodeText.numberOfElements(); i++){
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
        if (nodeTextIndex < nodeText.numberOfElements() && nodeText.getTextElement(nodeTextIndex).isToken(RBRACE)) {
            indentationAdj = indentationAdj.subList(0, indentationAdj.size() - Math.min(STANDARD_INDENTATION_SIZE, indentationAdj.size()));
        } else if (followedByUnindent) {
            indentationAdj = indentationAdj.subList(0, Math.max(0, indentationAdj.size() - STANDARD_INDENTATION_SIZE));
        }
        for (TextElement e : indentationAdj) {
            if ((nodeTextIndex< nodeText.numberOfElements()) && nodeText.getTextElement(nodeTextIndex).isSpaceOrTab()) {
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
