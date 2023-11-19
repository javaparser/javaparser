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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CalculatedSyntaxModel;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class DifferenceElementCalculator {

    // internally keep track of a node position in a List<CsmElement>
    public static class ChildPositionInfo {

        Node node;

        Integer position;

        ChildPositionInfo(Node node, Integer position) {
            this.node = node;
            this.position = position;
        }

        @Override
        public boolean equals(Object other) {
            if (other == null || !(other instanceof ChildPositionInfo))
                return false;
            ChildPositionInfo cpi = (ChildPositionInfo) other;
            // verify that the node content and the position are equal
            // because we can have nodes with the same content but in different lines
            // in this case we consider that nodes are not equals
            // If the nodes have no declared position they are considered equal.
            return this.node.equals(cpi.node) && (this.node.hasRange() == false && cpi.node.hasRange() == false || (this.node.hasRange() && cpi.node.hasRange() && this.node.getRange().get().contains(cpi.node.getRange().get())));
        }

        @Override
        public int hashCode() {
            return node.hashCode() + position.hashCode();
        }
    }

    static boolean matching(CsmElement a, CsmElement b) {
        if (a instanceof CsmChild) {
            if (b instanceof CsmChild) {
                CsmChild childA = (CsmChild) a;
                CsmChild childB = (CsmChild) b;
                return childA.getChild().equals(childB.getChild());
            }
            if (b instanceof CsmToken) {
                return false;
            }
            if (b instanceof CsmIndent) {
                return false;
            }
            if (b instanceof CsmUnindent) {
                return false;
            }
            throw new UnsupportedOperationException(a.getClass().getSimpleName() + " " + b.getClass().getSimpleName());
        }
        if (a instanceof CsmToken) {
            if (b instanceof CsmToken) {
                // fix #2382:
                // Tokens are described by their type AND their content
                // and TokenContentCalculator. By using .equals(), all
                // three values are compared.
                CsmToken childA = (CsmToken) a;
                CsmToken childB = (CsmToken) b;
                return childA.equals(childB);
            }
            if (b instanceof CsmChild) {
                return false;
            }
            if (b instanceof CsmIndent) {
                return false;
            }
            if (b instanceof CsmUnindent) {
                return false;
            }
            throw new UnsupportedOperationException(a.getClass().getSimpleName() + " " + b.getClass().getSimpleName());
        }
        if (a instanceof CsmIndent) {
            return b instanceof CsmIndent;
        }
        if (a instanceof CsmUnindent) {
            return b instanceof CsmUnindent;
        }
        throw new UnsupportedOperationException(a.getClass().getSimpleName() + " " + b.getClass().getSimpleName());
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
            }
            if (b instanceof CsmToken) {
                return false;
            }
            throw new UnsupportedOperationException(a.getClass().getSimpleName() + " " + b.getClass().getSimpleName());
        }
        if (a instanceof CsmToken) {
            if (b instanceof CsmToken) {
                CsmToken childA = (CsmToken) a;
                CsmToken childB = (CsmToken) b;
                return childA.getTokenType() == childB.getTokenType();
            }
            if (b instanceof CsmChild) {
                return false;
            }
        }
        throw new UnsupportedOperationException(a.getClass().getSimpleName() + " " + b.getClass().getSimpleName());
    }

    /**
     * Find the positions of all the given children.
     */
    private static List<ChildPositionInfo> findChildrenPositions(LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel) {
        List<ChildPositionInfo> positions = new ArrayList<>();
        for (int i = 0; i < calculatedSyntaxModel.elements.size(); i++) {
            CsmElement element = calculatedSyntaxModel.elements.get(i);
            if (element instanceof CsmChild) {
                positions.add(new ChildPositionInfo(((CsmChild) element).getChild(), i));
            }
        }
        return positions;
    }

    /**
     * Calculate the Difference between two CalculatedSyntaxModel elements, determining which elements were kept,
     * which were added and which were removed.
     */
    static List<DifferenceElement> calculate(LexicalDifferenceCalculator.CalculatedSyntaxModel original, LexicalDifferenceCalculator.CalculatedSyntaxModel after) {
        // For performance reasons we use the positions of matching children
        // to guide the calculation of the difference
        //
        // Suppose we have:
        // qwerty[A]uiop
        // qwer[A]uiop
        //
        // with [A] being a child and lowercase letters being tokens
        //
        // We would calculate the Difference between "qwerty" and "qwer" then we know the A is kept, and then we
        // would calculate the difference between "uiop" and "uiop"
        List<ChildPositionInfo> childrenInOriginal = findChildrenPositions(original);
        List<ChildPositionInfo> childrenInAfter = findChildrenPositions(after);
        List<ChildPositionInfo> commonChildren = new ArrayList<>(childrenInOriginal);
        commonChildren.retainAll(childrenInAfter);
        List<DifferenceElement> elements = new LinkedList<>();
        int originalIndex = 0;
        int afterIndex = 0;
        int commonChildrenIndex = 0;
        // undefined
        int posOfNextChildInOriginal = -1;
        // undefined
        int posOfNextChildInAfter = -1;
        // The algorithm is based on common child elements.
        // It first analyzes the elements preceding this child.
        // Then it keeps the common element and continues the analysis between the element
        // following this child and the common element in the list.
        while (commonChildrenIndex < commonChildren.size()) {
            ChildPositionInfo child = commonChildren.get(commonChildrenIndex++);
            // search the position of the node "child" in the original list of cms element
            final int currentPosOfNextChildInOriginal = posOfNextChildInOriginal;
            final int currentPosOfNextChildInAfter = posOfNextChildInAfter;
            posOfNextChildInOriginal = childrenInOriginal.stream().filter(i -> i.equals(child)).map(i -> i.position).filter(position -> position > currentPosOfNextChildInOriginal).findFirst().orElse(posOfNextChildInOriginal);
            // search the position of the node "child" in the modified list of cms element
            posOfNextChildInAfter = childrenInAfter.stream().filter(i -> i.equals(child)).map(i -> i.position).filter(position -> position > currentPosOfNextChildInAfter).findFirst().orElse(posOfNextChildInAfter);
            // Imagine that the common elements has been moved, for example in the case where the parameters of a method are reversed
            // In this case the afterIndex will be greater than the position of the child in
            // the list
            // For example : if {@code new Foo(a, b)} become {@code new Foo(b, a)}
            // Nota: in this example there is 3 child elements Foo, 'a' and 'b', others are tokens
            // In the orginal list the child element 'a' is at the position 5 and the
            // element 'b' is at the position 8
            // After reverting the list of parameters the child element 'a' is at the
            // position 8 and the element 'b' is at the position 5
            // When we deal with element 'b', it is in 5th position in the list after the
            // modification but the previous position in the list was that of element 'a'.
            if (originalIndex < posOfNextChildInOriginal || afterIndex < posOfNextChildInAfter) {
                // defines the sublist of elements located before the common element
                CalculatedSyntaxModel originalSub = originalIndex < posOfNextChildInOriginal ? original.sub(originalIndex, posOfNextChildInOriginal) : new CalculatedSyntaxModel(Collections.EMPTY_LIST);
                CalculatedSyntaxModel afterSub = afterIndex < posOfNextChildInAfter ? after.sub(afterIndex, posOfNextChildInAfter) : new CalculatedSyntaxModel(Collections.EMPTY_LIST);
                elements.addAll(calculateImpl(originalSub, afterSub));
            }
            if (afterIndex <= posOfNextChildInAfter) {
                // we need to keep the current common node
                elements.add(new Kept(new CsmChild(child.node)));
            } else {
                // In this case the current node was not found in the list after change
                // so we need to remove it.
                elements.add(new Removed(new CsmChild(child.node)));
            }
            originalIndex = originalIndex <= posOfNextChildInOriginal ? posOfNextChildInOriginal + 1 : originalIndex;
            afterIndex = afterIndex <= posOfNextChildInAfter ? posOfNextChildInAfter + 1 : afterIndex;
        }
        if (originalIndex < original.elements.size() || afterIndex < after.elements.size()) {
            CalculatedSyntaxModel originalSub = originalIndex < original.elements.size() ? original.sub(originalIndex, original.elements.size()) : new CalculatedSyntaxModel(Collections.EMPTY_LIST);
            CalculatedSyntaxModel afterSub = afterIndex < after.elements.size() ? after.sub(afterIndex, after.elements.size()) : new CalculatedSyntaxModel(Collections.EMPTY_LIST);
            elements.addAll(calculateImpl(originalSub, afterSub));
        }
        return elements;
    }

    private static void considerRemoval(NodeText nodeTextForChild, List<DifferenceElement> elements) {
        for (TextElement el : nodeTextForChild.getElements()) {
            if (el instanceof ChildTextElement) {
                ChildTextElement cte = (ChildTextElement) el;
                considerRemoval(LexicalPreservingPrinter.getOrCreateNodeText(cte.getChild()), elements);
            } else if (el instanceof TokenTextElement) {
                TokenTextElement tte = (TokenTextElement) el;
                elements.add(new Removed(new CsmToken(tte.getTokenKind(), tte.getText())));
            } else {
                throw new UnsupportedOperationException(el.toString());
            }
        }
    }

    private static int considerRemoval(CsmElement removedElement, int originalIndex, List<DifferenceElement> elements) {
        boolean dealtWith = false;
        if (removedElement instanceof CsmChild) {
            CsmChild removedChild = (CsmChild) removedElement;
            if (removedChild.getChild() instanceof Type && removedChild.getChild().getParentNode().isPresent() && removedChild.getChild().getParentNode().get() instanceof VariableDeclarator) {
                NodeText nodeTextForChild = LexicalPreservingPrinter.getOrCreateNodeText(removedChild.getChild());
                considerRemoval(nodeTextForChild, elements);
                originalIndex++;
                dealtWith = true;
            }
        }
        if (!dealtWith) {
            elements.add(new Removed(removedElement));
            originalIndex++;
        }
        return originalIndex;
    }

    private static List<DifferenceElement> calculateImpl(LexicalDifferenceCalculator.CalculatedSyntaxModel original, LexicalDifferenceCalculator.CalculatedSyntaxModel after) {
        List<DifferenceElement> elements = new LinkedList<>();
        int originalIndex = 0;
        int afterIndex = 0;
        // We move through the two CalculatedSyntaxModel, moving both forward when we have a match
        // and moving just one side forward when we have an element kept or removed
        do {
            if (originalIndex < original.elements.size() && afterIndex >= after.elements.size()) {
                CsmElement removedElement = original.elements.get(originalIndex);
                originalIndex = considerRemoval(removedElement, originalIndex, elements);
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
                        elements.add(new Reshuffled((CsmMix) nextOriginal, (CsmMix) nextAfter));
                    }
                    originalIndex++;
                    afterIndex++;
                } else if (matching(nextOriginal, nextAfter)) {
                    elements.add(new Kept(nextOriginal));
                    originalIndex++;
                    afterIndex++;
                } else if (replacement(nextOriginal, nextAfter)) {
                    originalIndex = considerRemoval(nextOriginal, originalIndex, elements);
                    elements.add(new Added(nextAfter));
                    afterIndex++;
                } else {
                    // We can try to remove the element or add it and look which one leads to the lower difference
                    List<DifferenceElement> addingElements = calculate(original.from(originalIndex), after.from(afterIndex + 1));
                    List<DifferenceElement> removingElements = null;
                    if (cost(addingElements) > 0) {
                        removingElements = calculate(original.from(originalIndex + 1), after.from(afterIndex));
                    }
                    if (removingElements == null || cost(removingElements) > cost(addingElements)) {
                        elements.add(new Added(nextAfter));
                        afterIndex++;
                    } else {
                        elements.add(new Removed(nextOriginal));
                        originalIndex++;
                    }
                }
            }
        } while (originalIndex < original.elements.size() || afterIndex < after.elements.size());
        return elements;
    }

    private static long cost(List<DifferenceElement> elements) {
        return elements.stream().filter(e -> !(e instanceof Kept)).count();
    }

    /**
     * Remove from the difference all the elements related to indentation.
     * This is mainly intended for test purposes.
     */
    static void removeIndentationElements(List<DifferenceElement> elements) {
        elements.removeIf(el -> el.getElement() instanceof CsmIndent || el.getElement() instanceof CsmUnindent);
    }
}
