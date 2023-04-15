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
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.concretesyntaxmodel.CsmUnindent;

public class Added implements DifferenceElement {

    private final CsmElement element;

    Added(CsmElement element) {
        this.element = element;
    }

    @Override
    public String toString() {
        return "Added{" + element + '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
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

    @Override
    public boolean isRemoved() {
        return false;
    }

    @Override
    public boolean isKept() {
        return false;
    }

    public boolean isIndent() {
        return element instanceof CsmIndent;
    }

    public boolean isUnindent() {
        return element instanceof CsmUnindent;
    }

    private boolean isToken() {
        return element instanceof CsmToken;
    }

    public TextElement toTextElement() {
        if (element instanceof LexicalDifferenceCalculator.CsmChild) {
            return new ChildTextElement(((LexicalDifferenceCalculator.CsmChild) element).getChild());
        } else if (element instanceof CsmToken) {
            return new TokenTextElement(((CsmToken) element).getTokenType(), ((CsmToken) element).getContent(null));
        } else {
            throw new UnsupportedOperationException(element.getClass().getSimpleName());
        }
    }

    /*
     * If the {@code DifferenceElement} wraps an EOL token then this method returns a new wrapped {@code CsmElement}
     * with the specified line separator. The line separator parameter must be a CsmToken with a valid line separator.
     */
    @Override
    public DifferenceElement replaceEolTokens(CsmElement lineSeparator) {
        return isNewLine() ? new Added(lineSeparator) : this;
    }

    /*
     * Return true if the wrapped {@code CsmElement} is a new line token
     */
    public boolean isNewLine() {
        return isToken() && ((CsmToken) element).isNewLine();
    }
}
