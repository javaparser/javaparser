/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.printer.concretesyntaxmodel;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.SourcePrinter;

import java.util.Arrays;
import java.util.List;

import static com.github.javaparser.TokenTypes.*;
import static com.github.javaparser.utils.Utils.EOL;

public interface CsmElement {

    void prettyPrint(Node node, SourcePrinter printer);

    static CsmElement child(ObservableProperty property) {
        return new CsmSingleReference(property);
    }

    static CsmElement attribute(ObservableProperty property) {
        return new CsmAttribute(property);
    }

    static CsmElement sequence(CsmElement... elements) {
        return new CsmSequence(Arrays.asList(elements));
    }

    static CsmElement string(int tokenType, String content) {
        return new CsmToken(tokenType, content);
    }

    static CsmElement string(int tokenType) {
        return new CsmToken(tokenType);
    }

    static CsmElement stringToken(ObservableProperty property) {
        return new CsmString(property);
    }

    static CsmElement charToken(ObservableProperty property) {
        return new CsmChar(property);
    }

    static CsmElement token(int tokenType) {
        return new CsmToken(tokenType);
    }

    static CsmElement token(int tokenType, CsmToken.TokenContentCalculator tokenContentCalculator) {
        return new CsmToken(tokenType, tokenContentCalculator);
    }

    static CsmElement conditional(ObservableProperty property, CsmConditional.Condition condition, CsmElement thenElement) {
        return new CsmConditional(property, condition, thenElement);
    }

    static CsmElement conditional(ObservableProperty property, CsmConditional.Condition condition, CsmElement thenElement, CsmElement elseElement) {
        return new CsmConditional(property, condition, thenElement, elseElement);
    }

    static CsmElement conditional(List<ObservableProperty> properties, CsmConditional.Condition condition, CsmElement thenElement, CsmElement elseElement) {
        return new CsmConditional(properties, condition, thenElement, elseElement);
    }

    static CsmElement space() {
        return new CsmToken(spaceTokenKind(), " ");
    }

    static CsmElement semicolon() {
        return new CsmToken(GeneratedJavaParserConstants.SEMICOLON);
    }

    static CsmElement comment() { return new CsmComment(); }

    static CsmElement newline() {
        return new CsmToken(eolTokenKind(), EOL);
    }

    static CsmElement none() {
        return new CsmNone();
    }

    static CsmElement comma() {
        return new CsmToken(GeneratedJavaParserConstants.COMMA);
    }

    static CsmElement list(ObservableProperty property) {
        return new CsmList(property);
    }

    static CsmElement list(ObservableProperty property, CsmElement separator) {
        return new CsmList(property, CsmElement.none(), separator, new CsmNone(), new CsmNone());
    }

    static CsmElement list(ObservableProperty property, CsmElement separator, CsmElement preceeding, CsmElement following) {
        return new CsmList(property, none(), separator, preceeding, following);
    }

    static CsmElement list(ObservableProperty property, CsmElement separatorPre, CsmElement separatorPost, CsmElement preceeding, CsmElement following) {
        return new CsmList(property, separatorPre, separatorPost, preceeding, following);
    }

    static CsmElement orphanCommentsEnding() {
        return new CsmOrphanCommentsEnding();
    }

    static CsmElement orphanCommentsBeforeThis() {
        // FIXME
        return new CsmNone();
    }

    static CsmElement indent() {
        return new CsmIndent();
    }

    static CsmElement unindent() {
        return new CsmUnindent();
    }

    static CsmElement block(CsmElement content) {
        return sequence(token(GeneratedJavaParserConstants.LBRACE), indent(), content, unindent(), token(GeneratedJavaParserConstants.RBRACE));
    }
}
