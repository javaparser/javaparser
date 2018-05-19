package com.github.javaparser.printer.lexicalpreservation.difference;

import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.concretesyntaxmodel.CsmUnindent;
import com.github.javaparser.printer.lexicalpreservation.ChildTextElement;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator;
import com.github.javaparser.printer.lexicalpreservation.TextElement;
import com.github.javaparser.printer.lexicalpreservation.TokenTextElement;

public class Added implements DifferenceElement {
    final CsmElement element;

    public Added(CsmElement element) {
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

    public boolean isIndent() { return element instanceof CsmIndent; }

    public boolean isUnindent() { return element instanceof CsmUnindent; }

    public TextElement toTextElement() {
        if (element instanceof LexicalDifferenceCalculator.CsmChild) {
            return new ChildTextElement(((LexicalDifferenceCalculator.CsmChild) element).getChild());
        } else if (element instanceof CsmToken) {
            return new TokenTextElement(((CsmToken) element).getTokenType(), ((CsmToken) element).getContent(null));
        } else {
            throw new UnsupportedOperationException(element.getClass().getSimpleName());
        }
    }
}
