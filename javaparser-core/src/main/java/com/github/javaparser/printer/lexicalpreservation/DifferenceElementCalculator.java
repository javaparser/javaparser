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

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.concretesyntaxmodel.CsmUnindent;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

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
            if ( other == null || !(other instanceof ChildPositionInfo))
                return false;
            ChildPositionInfo cpi = (ChildPositionInfo)other;
            // verify that the node content and the position are equal
            // because we can have nodes with the same content but in different lines
            // in this case we consider that nodes are not equals
            return this.node.equals(cpi.node)
                    && this.node.getRange().isPresent() && cpi.node.getRange().isPresent()
                    && this.node.getRange().get().contains(cpi.node.getRange().get());
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
                return childA.getChildNode().equals(childB.getChildNode());
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
                // fix #2382:
                // Tokens are described by their type AND their content
                // and TokenContentCalculator. By using .equals(), all
                // three values are compared.
                CsmToken childA = (CsmToken)a;
                CsmToken childB = (CsmToken)b;
                // TODO: Consider mixed line endings as equal? (equivalent?)
                return childA.equals(childB);
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
                return childA.getChildNode().getClass().equals(childB.getChildNode().getClass());
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
    private static List<ChildPositionInfo> findChildrenPositions(LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel) {
        List<ChildPositionInfo> positions = new ArrayList<>();
        for (int i=0;i<calculatedSyntaxModel.elements.size();i++) {
            CsmElement element = calculatedSyntaxModel.elements.get(i);
            if (element instanceof CsmChild) {
                positions.add(new ChildPositionInfo(((CsmChild)element).getChildNode(), i));
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
        //   qwerty[A]uiop
        //   qwer[A]uiop
        //
        // with [A] being a child and lowercase letters being tokens
        //
        // We would calculate the Difference between "qwerty" and "qwer" then we know the A is kept, and then we
        // would calculate the difference between "uiop" and "uiop"

        List<ChildPositionInfo> childrenInOriginal = findChildrenPositions(original);
        List<ChildPositionInfo> childrenInAfter = findChildrenPositions(after);

        List<ChildPositionInfo> commonChildren = new ArrayList<>(childrenInOriginal);
        commonChildren.retainAll(childrenInAfter);

        List<DifferenceElement> differenceElements = new LinkedList<>();

        int originalIndex = 0;
        int afterIndex = 0;
        int commonChildrenIndex = 0;
        while (commonChildrenIndex < commonChildren.size()) {
            ChildPositionInfo child = commonChildren.get(commonChildrenIndex);
            // search the position of the node "child" in the original list of cms element
            int posOfNextChildInOriginal = childrenInOriginal.stream().filter(i->i.equals(child)).map(i->i.position).findFirst().get();
            // search the position of the node "child" in the modified list of cms element
            int posOfNextChildInAfter = childrenInAfter.stream().filter(i->i.equals(child)).map(i->i.position).findFirst().get();


            //
            boolean unhandledDifferencesRemain = originalIndex < posOfNextChildInOriginal || afterIndex < posOfNextChildInAfter;
            if (unhandledDifferencesRemain) {
                List<DifferenceElement> changeDifferences = calculateImpl(
                        original.sub(originalIndex, posOfNextChildInOriginal),
                        after.sub(afterIndex, posOfNextChildInAfter)
                );
                // Add differences
                differenceElements.addAll(changeDifferences);
            }

            differenceElements.add(new Kept(new CsmChild(child.node)));
            originalIndex = posOfNextChildInOriginal + 1;
            afterIndex = posOfNextChildInAfter + 1;

            // Move to next common child.
            commonChildrenIndex++;
        }


        // If unhandled differences remain after we have processed the common children...
        boolean unhandledDifferencesRemain = originalIndex < original.elements.size() || afterIndex < after.elements.size();
        if (unhandledDifferencesRemain) {
            List<DifferenceElement> changeDifferences = calculateImpl(
                    original.sub(originalIndex, original.elements.size()),
                    after.sub(afterIndex, after.elements.size())
            );
            // Add differences
            differenceElements.addAll(changeDifferences);
        }
        return differenceElements;
    }

    private static void considerRemoval(NodeText nodeTextForChild, List<DifferenceElement> differenceElements) {
        for (TextElement el : nodeTextForChild.getElements()) {
            if (el instanceof ChildTextElement) {
                ChildTextElement cte = (ChildTextElement) el;
                considerRemoval(LexicalPreservingPrinter.getOrCreateNodeText(cte.getChild()), differenceElements);
            } else if (el instanceof TokenTextElement) {
                TokenTextElement tte = (TokenTextElement) el;
                differenceElements.add(new Removed(new CsmToken(tte.getTokenKind(), tte.getText())));
            } else {
                throw new UnsupportedOperationException(el.toString());
            }
        }
    }

    private static int considerRemoval(CsmElement removedElement, int originalIndex, List<DifferenceElement> differenceElements) {
        boolean dealtWith = false;
        if (removedElement instanceof CsmChild) {
            Node removedChildNode = ((CsmChild) removedElement).getChildNode();
            boolean parentOfRemovedChildIsVariableDeclarator = removedChildNode instanceof Type &&
                    removedChildNode.getParentNode().isPresent() &&
                    removedChildNode.getParentNode().get() instanceof VariableDeclarator;
            if (parentOfRemovedChildIsVariableDeclarator) {
                NodeText nodeTextForChild = LexicalPreservingPrinter.getOrCreateNodeText(removedChildNode);
                considerRemoval(nodeTextForChild, differenceElements);
                originalIndex++;
                dealtWith = true;
            }
        }
        if (!dealtWith) {
            differenceElements.add(new Removed(removedElement));
            originalIndex++;
        }
        return originalIndex;
    }

    // TODO: Rename me (what is "impl"?).
    static List<DifferenceElement> calculateImpl(LexicalDifferenceCalculator.CalculatedSyntaxModel original, LexicalDifferenceCalculator.CalculatedSyntaxModel after) {
        List<DifferenceElement> differenceElements = new LinkedList<>();

        int originalIndex = 0;
        int afterIndex = 0;

        // We move through the two CalculatedSyntaxModel, moving both forward when we have a match
        // and moving just one side forward when we have an element kept or removed

        boolean originalElementsRemaining = originalIndex < original.elements.size();
        boolean afterElementsRemaining = afterIndex < after.elements.size();
        do {
            // TODO: These "exhausted" variables can be defined as the inverse of differenceElements remaining.
            boolean exhaustedAfterElements = afterIndex >= after.elements.size();
            boolean exhaustedOriginalElements = originalIndex >= original.elements.size();

            if (originalElementsRemaining && exhaustedAfterElements) {
                // Elements are present in the original, but not after.
                // Thus can shortcut as all remaining differenceElements must have been removed.
                CsmElement removedElement = original.elements.get(originalIndex);
                originalIndex = considerRemoval(removedElement, originalIndex, differenceElements);
            } else if (exhaustedOriginalElements && afterElementsRemaining) {
                // No original differenceElements remain but there are still more differenceElements after.
                // Thus can shortcut as all remaining differenceElements must have been added.
                differenceElements.add(new Added(after.elements.get(afterIndex)));
                afterIndex++;
            } else {
                // Still differenceElements remaining before/after that must be compared.
                // Thus, must look more closely to determine if they have been added/removed.
                CsmElement nextOriginal = original.elements.get(originalIndex);
                CsmElement nextAfter = after.elements.get(afterIndex);

                if ((nextOriginal instanceof CsmMix) && (nextAfter instanceof CsmMix)) {
                    if (((CsmMix) nextAfter).getElements().equals(((CsmMix) nextOriginal).getElements())) {
                        // They are equal -- we are just going to keep everything as it is.
                        // Thus we can shortcut as there is no reason to deal with a Reshuffled.
                        ((CsmMix) nextAfter).getElements().forEach(el -> differenceElements.add(new Kept(el)));
                    } else {
                        differenceElements.add(new Reshuffled((CsmMix) nextOriginal, (CsmMix) nextAfter));
                    }
                    originalIndex++;
                    afterIndex++;
                } else if (matching(nextOriginal, nextAfter)) {
                    // Flag as kept, and move to next element
                    differenceElements.add(new Kept(nextOriginal));
                    originalIndex++;
                    afterIndex++;
                } else if (replacement(nextOriginal, nextAfter)) {
                    originalIndex = considerRemoval(nextOriginal, originalIndex, differenceElements);
                    differenceElements.add(new Added(nextAfter));
                    afterIndex++;
                } else {
                    // We can try to remove the element or add it and look which one leads to the least difference (similar to Levenshtein distance between strings)
                    List<DifferenceElement> addingElements = calculate(original.from(originalIndex), after.from(afterIndex + 1));
                    List<DifferenceElement> removingElements = new ArrayList<>();
                    if (costOfDifferences(addingElements) > 0) {
                        removingElements = calculate(original.from(originalIndex + 1), after.from(afterIndex));
                    }

                    if (costOfDifferences(addingElements) < costOfDifferences(removingElements)) {
                        // If adding is more optimal than removal:
                        differenceElements.add(new Added(nextAfter));
                        afterIndex++; // TODO: Document why after
                    } else if (costOfDifferences(addingElements) > costOfDifferences(removingElements)) {
                        // If removal is more optimal than adding:
                        differenceElements.add(new Removed(nextOriginal));
                        originalIndex++; // TODO: Document why original
                    } else {
                        // If removal and adding are equivalent -- default to adding: // TODO: Document why? Note defaulting to removal fails...
                        differenceElements.add(new Added(nextAfter));
                        afterIndex++; // TODO: Document why after
                    }
                }
            }

            // Variables to indicate if we have reached the end of either the originals or the afters.
            // Note: Deliberately updated at the end, so that the while() condition uses up-to-date values.
            originalElementsRemaining = originalIndex < original.elements.size();
            afterElementsRemaining = afterIndex < after.elements.size();

        } while (originalElementsRemaining || afterElementsRemaining);

        return differenceElements;
    }

    /**
     * @return The number of changes (additions/removals) as the cost.
     */
    private static long costOfDifferences(List<DifferenceElement> differenceElements) {
        return differenceElements.stream().filter(e -> !(e instanceof Kept)).count();
    }


    /**
     * Remove from the difference all the differenceElements related to indentation.
     * This is mainly intended for test purposes.
     */
    static void removeIndentationElements(List<DifferenceElement> differenceElements) {
        differenceElements.removeIf(el -> el.getElement() instanceof CsmIndent || el.getElement() instanceof CsmUnindent);
    }
}
