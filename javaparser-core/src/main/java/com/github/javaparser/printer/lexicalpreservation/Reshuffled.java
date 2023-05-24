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

import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import java.util.List;
import java.util.stream.Collectors;

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
        return "Reshuffled{" + nextOrder + ", previous=" + previousOrder + '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        Reshuffled that = (Reshuffled) o;
        if (!previousOrder.equals(that.previousOrder))
            return false;
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

    @Override
    public boolean isKept() {
        return false;
    }

    /*
     * If the {@code DifferenceElement} wraps an EOL token then this method returns a new {@code DifferenceElement}
     * with all eof token replaced by the specified line separator. The line separator parameter must be a CsmToken with a valid line separator.
     */
    @Override
    public DifferenceElement replaceEolTokens(CsmElement lineSeparator) {
        CsmMix modifiedNextOrder = new CsmMix(replaceTokens(nextOrder.getElements(), lineSeparator));
        CsmMix modifiedPreviousOrder = new CsmMix(replaceTokens(previousOrder.getElements(), lineSeparator));
        return new Reshuffled(modifiedPreviousOrder, modifiedNextOrder);
    }

    /*
     * Replaces all eol tokens in the list by the specified line separator token 
     */
    private List<CsmElement> replaceTokens(List<CsmElement> elements, CsmElement lineSeparator) {
        return elements.stream().map(element -> isNewLineToken(element) ? lineSeparator : element).collect(Collectors.toList());
    }

    /*
     * Return true if the wrapped {@code CsmElement} is a new line token
     */
    private boolean isNewLineToken(CsmElement element) {
        return isToken(element) && ((CsmToken) element).isNewLine();
    }

    private boolean isToken(CsmElement element) {
        return element instanceof CsmToken;
    }
}
