package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.concretesyntaxmodel.*;

import java.util.*;

public class DifferenceElementCalculator {
    static boolean matching(CsmElement a, CsmElement b) {
        if (a instanceof LexicalDifferenceCalculator.CsmChild) {
            if (b instanceof LexicalDifferenceCalculator.CsmChild) {
                LexicalDifferenceCalculator.CsmChild childA = (LexicalDifferenceCalculator.CsmChild) a;
                LexicalDifferenceCalculator.CsmChild childB = (LexicalDifferenceCalculator.CsmChild) b;
                return childA.getChild().equals(childB.getChild());
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
                CsmToken childA = (CsmToken)a;
                CsmToken childB = (CsmToken)b;
                return childA.getTokenType() == childB.getTokenType();
            } else if (b instanceof LexicalDifferenceCalculator.CsmChild) {
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
        if (a instanceof LexicalDifferenceCalculator.CsmChild) {
            if (b instanceof LexicalDifferenceCalculator.CsmChild) {
                LexicalDifferenceCalculator.CsmChild childA = (LexicalDifferenceCalculator.CsmChild) a;
                LexicalDifferenceCalculator.CsmChild childB = (LexicalDifferenceCalculator.CsmChild) b;
                return childA.getChild().getClass().equals(childB.getChild().getClass());
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
            } else if (b instanceof LexicalDifferenceCalculator.CsmChild) {
                return false;
            }
        }
        throw new UnsupportedOperationException(a.getClass().getSimpleName()+ " "+b.getClass().getSimpleName());
    }

    /**
     * Find the positions of all the given children.
     */
    private static Map<Node, Integer> findChildrenPositions(LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel) {
        Map<Node, Integer> positions = new HashMap<>();
        for (int i=0;i<calculatedSyntaxModel.elements.size();i++) {
            CsmElement element = calculatedSyntaxModel.elements.get(i);
            if (element instanceof LexicalDifferenceCalculator.CsmChild) {
                positions.put(((LexicalDifferenceCalculator.CsmChild)element).getChild(), i);
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

        Map<Node, Integer> childrenInOriginal = findChildrenPositions(original);
        Map<Node, Integer> childrenInAfter = findChildrenPositions(after);

        List<Node> commonChildren = new LinkedList<>(childrenInOriginal.keySet());
        commonChildren.retainAll(childrenInAfter.keySet());
        commonChildren.sort(Comparator.comparingInt(childrenInOriginal::get));

        List<DifferenceElement> elements = new LinkedList<>();

        int originalIndex = 0;
        int afterIndex = 0;
        int commonChildrenIndex = 0;
        while (commonChildrenIndex < commonChildren.size()) {
            Node child = commonChildren.get(commonChildrenIndex++);
            int posOfNextChildInOriginal = childrenInOriginal.get(child);
            int posOfNextChildInAfter    = childrenInAfter.get(child);
            if (originalIndex < posOfNextChildInOriginal || afterIndex < posOfNextChildInAfter) {
                elements.addAll(calculateImpl(original.sub(originalIndex, posOfNextChildInOriginal), after.sub(afterIndex, posOfNextChildInAfter)));
            }
            elements.add(new Kept(new LexicalDifferenceCalculator.CsmChild(child)));
            originalIndex = posOfNextChildInOriginal + 1;
            afterIndex = posOfNextChildInAfter + 1;
        }

        if (originalIndex < original.elements.size() || afterIndex < after.elements.size()) {
            elements.addAll(calculateImpl(original.sub(originalIndex, original.elements.size()), after.sub(afterIndex, after.elements.size())));
        }
        return elements;
    }

    private static List<DifferenceElement> calculateImpl(LexicalDifferenceCalculator.CalculatedSyntaxModel original, LexicalDifferenceCalculator.CalculatedSyntaxModel after) {
        List<DifferenceElement> elements = new LinkedList<>();

        int originalIndex = 0;
        int afterIndex = 0;

        // We move through the two CalculatedSyntaxModel, moving both forward when we have a match
        // and moving just one side forward when we have an element kept or removed

        do {
            if (originalIndex < original.elements.size() && afterIndex >= after.elements.size()) {
                elements.add(new Removed(original.elements.get(originalIndex)));
                originalIndex++;
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
                        elements.add(new Reshuffled((CsmMix)nextOriginal, (CsmMix)nextAfter));
                    }
                    originalIndex++;
                    afterIndex++;
                } else if (matching(nextOriginal, nextAfter)) {
                    elements.add(new Kept(nextOriginal));
                    originalIndex++;
                    afterIndex++;
                } else if (replacement(nextOriginal, nextAfter)) {
                    elements.add(new Removed(nextOriginal));
                    elements.add(new Added(nextAfter));
                    originalIndex++;
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

    interface DifferenceElement {
        static DifferenceElement added(CsmElement element) {
            return new Added(element);
        }

        static DifferenceElement removed(CsmElement element) {
            return new Removed(element);
        }

        static DifferenceElement kept(CsmElement element) {
            return new Kept(element);
        }

        /**
         * Return the CsmElement considered in this DifferenceElement.
         */
        CsmElement getElement();

        boolean isAdded();
    }

    static class Added implements DifferenceElement {
        final CsmElement element;

        Added(CsmElement element) {
            this.element = element;
        }

        @Override
        public String toString() {
            return "Added{" + element + '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Added added = (Added) o;

            return element.equals(added.element);
        }

        @Override
        public int hashCode() {
            return element.hashCode();
        }

        @Override
        public CsmElement getElement() {
            return element;
        }

        @Override
        public boolean isAdded() {
            return true;
        }

        boolean isIndent() { return element instanceof CsmIndent; }

        boolean isUnindent() { return element instanceof CsmUnindent; }

        TextElement toTextElement() {
            if (element instanceof LexicalDifferenceCalculator.CsmChild) {
                return new ChildTextElement(((LexicalDifferenceCalculator.CsmChild) element).getChild());
            } else if (element instanceof CsmToken) {
                return new TokenTextElement(((CsmToken) element).getTokenType(), ((CsmToken) element).getContent(null));
            } else {
                throw new UnsupportedOperationException(element.getClass().getSimpleName());
            }
        }
    }

    /**
     * Elements in a CsmMix have been reshuffled. It could also mean that
     * some new elements have been added or removed to the mix.
     */
    static class Reshuffled implements DifferenceElement {
        final CsmMix previousOrder;
        final CsmMix element;

        Reshuffled(CsmMix previousOrder, CsmMix element) {
            this.previousOrder = previousOrder;
            this.element = element;
        }

        @Override
        public String toString() {
            return "Reshuffled{" + element + ", previous="+ previousOrder+ '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Reshuffled that = (Reshuffled) o;

            if (!previousOrder.equals(that.previousOrder)) return false;
            return element.equals(that.element);
        }

        @Override
        public int hashCode() {
            int result = previousOrder.hashCode();
            result = 31 * result + element.hashCode();
            return result;
        }

        @Override
        public CsmMix getElement() {
            return element;
        }

        @Override
        public boolean isAdded() {
            return false;
        }
    }

    static class Kept implements DifferenceElement {
        final CsmElement element;

        Kept(CsmElement element) {
            this.element = element;
        }

        @Override
        public String toString() {
            return "Kept{" + element + '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Kept kept = (Kept) o;

            return element.equals(kept.element);
        }

        @Override
        public int hashCode() {
            return element.hashCode();
        }

        @Override
        public CsmElement getElement() {
            return element;
        }

        int getTokenType() {
            if (isToken()) {
                CsmToken csmToken = (CsmToken) element;
                return csmToken.getTokenType();
            }

            throw new IllegalStateException("Kept is not a " + CsmToken.class.getSimpleName());
        }

        @Override
        public boolean isAdded() {
            return false;
        }

        boolean isIndent() { return element instanceof CsmIndent; }

        boolean isUnindent() { return element instanceof CsmUnindent; }

        boolean isToken() { return element instanceof CsmToken; }

        boolean isChild() { return element instanceof LexicalDifferenceCalculator.CsmChild; }

        boolean isPrimitiveType() {
            if (isChild()) {
                LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) element;
                return csmChild.getChild() instanceof PrimitiveType;
            }

            return false;
        }

        boolean isWhiteSpace() {
            if(isToken()) {
                CsmToken csmToken = (CsmToken) element;
                return csmToken.isWhiteSpace();
            }

            return false;
        }

        boolean isWhiteSpaceOrComment() {
            if (isToken()) {
                CsmToken csmToken = (CsmToken) element;
                return TokenTypes.isWhitespaceOrComment(csmToken.getTokenType());
            }

            return false;
        }
    }

    static class Removed implements DifferenceElement {
        final CsmElement element;

        Removed(CsmElement element) {
            this.element = element;
        }

        @Override
        public String toString() {
            return "Removed{" + element + '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Removed removed = (Removed) o;

            return element.equals(removed.element);
        }

        @Override
        public int hashCode() {
            return element.hashCode();
        }

        @Override
        public CsmElement getElement() {
            return element;
        }

        Node getChild() {
            if (isChild()) {
                LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) element;
                return csmChild.getChild();
            }

            throw new IllegalStateException("Removed is not a " + LexicalDifferenceCalculator.CsmChild.class.getSimpleName());
        }

        int getTokenType() {
            if (isToken()) {
                CsmToken csmToken = (CsmToken) element;
                return csmToken.getTokenType();
            }

            throw new IllegalStateException("Removed is not a " + CsmToken.class.getSimpleName());
        }

        @Override
        public boolean isAdded() {
            return false;
        }

        boolean isToken() { return element instanceof CsmToken; }

        boolean isChild() { return element instanceof LexicalDifferenceCalculator.CsmChild; }

        boolean isPrimitiveType() {
            if (isChild()) {
                LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) element;
                return csmChild.getChild() instanceof PrimitiveType;
            }

            return false;
        }

        boolean isWhiteSpace() {
            if(isToken()) {
                CsmToken csmToken = (CsmToken) element;
                return csmToken.isWhiteSpace();
            }

            return false;
        }
    }

    static long cost(List<DifferenceElement> elements) {
        return elements.stream().filter(e -> !(e instanceof DifferenceElementCalculator.Kept)).count();
    }


    /**
     * Remove from the difference all the elements related to indentation.
     * This is mainly intended for test purposes.
     */
    static void removeIndentationElements(List<DifferenceElement> elements) {
        elements.removeIf(el -> el.getElement() instanceof CsmIndent || el.getElement() instanceof CsmUnindent);
    }
}
