package com.github.javaparser.printer.lexicalpreservation.difference;

import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.lexicalpreservation.DifferenceElementCalculator;

public interface DifferenceElement {
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
    public CsmElement getElement();

    public boolean isAdded();
}
