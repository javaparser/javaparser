package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;

/**
 * Elements in a CsmMix have been reshuffled. It could also mean that
 * some new elements have been added or removed to the mix.
 */
public class Reshuffled implements DifferenceElement {
    private final CsmMix previousOrder;
    private final CsmMix nextOrder;

    Reshuffled(CsmMix previousOrder, CsmMix nextOrder) {
        this.previousOrder = previousOrder;
        this.nextOrder = nextOrder;
    }

    @Override
    public String toString() {
        return "Reshuffled{" + nextOrder + ", previous="+ previousOrder+ '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Reshuffled that = (Reshuffled) o;

        if (!previousOrder.equals(that.previousOrder)) return false;
        return nextOrder.equals(that.nextOrder);
    }

    @Override
    public int hashCode() {
        int result = previousOrder.hashCode();
        result = 31 * result + nextOrder.hashCode();
        return result;
    }

    @Override
    public CsmMix getElement() {
        return nextOrder;
    }

    public CsmMix getPreviousOrder() {
        return previousOrder;
    }

    public CsmMix getNextOrder() {
        return nextOrder;
    }

    @Override
    public boolean isAdded() {
        return false;
    }

    @Override
    public boolean isRemoved() {
        return false;
    }
}
