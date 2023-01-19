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

import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.concretesyntaxmodel.CsmUnindent;

public class Kept implements DifferenceElement {

    private final CsmElement element;

    Kept(CsmElement element) {
        this.element = element;
    }

    @Override
    public String toString() {
        return "Kept{" + element + '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
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

    public int getTokenType() {
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

    @Override
    public boolean isRemoved() {
        return false;
    }

    @Override
    public boolean isKept() {
        return true;
    }

    public boolean isIndent() {
        return element instanceof CsmIndent;
    }

    public boolean isUnindent() {
        return element instanceof CsmUnindent;
    }

    public boolean isToken() {
        return element instanceof CsmToken;
    }

    public boolean isPrimitiveType() {
        if (isChild()) {
            LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) element;
            return csmChild.getChild() instanceof PrimitiveType;
        }
        return false;
    }

    public boolean isWhiteSpace() {
        if (isToken()) {
            CsmToken csmToken = (CsmToken) element;
            return csmToken.isWhiteSpace();
        }
        return false;
    }

    public boolean isWhiteSpaceOrComment() {
        if (isToken()) {
            CsmToken csmToken = (CsmToken) element;
            return TokenTypes.isWhitespaceOrComment(csmToken.getTokenType());
        }
        return false;
    }

    public boolean isNewLine() {
        if (isToken()) {
            CsmToken csmToken = (CsmToken) element;
            return csmToken.isNewLine();
        }
        return false;
    }
}
