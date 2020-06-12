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

package com.github.javaparser.printer.concretesyntaxmodel;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.utils.LineSeparator;

import java.util.Arrays;
import java.util.List;

import static com.github.javaparser.TokenTypes.eolTokenKind;
import static com.github.javaparser.TokenTypes.spaceTokenKind;

public interface CsmElement {

    CsmElement addToContextNote(String contextNote);

    String getContextNote();


    void prettyPrint(Node node, SourcePrinter printer);

    static CsmElement child(ObservableProperty property) {
        return new CsmSingleReference(property); //.addToContextNote("CSM");
    }

    static CsmElement attribute(ObservableProperty property) {
        return new CsmAttribute(property); //.addToContextNote("CSM");
    }

    static CsmElement sequence(CsmElement... elements) {
        return new CsmSequence(Arrays.asList(elements)); //.addToContextNote("CSM");
    }

    static CsmElement string(int tokenType, String content) {
        return new CsmToken(tokenType, content); //.addToContextNote("CSM");
    }

    static CsmElement string(int tokenType) {
        return new CsmToken(tokenType); //.addToContextNote("CSM");
    }

    static CsmElement stringToken(ObservableProperty property) {
        return new CsmString(property); //.addToContextNote("CSM");
    }

    static CsmElement textBlockToken(ObservableProperty property) {
        return new CsmString(property); //.addToContextNote("CSM");
    }

    static CsmElement charToken(ObservableProperty property) {
        return new CsmChar(property); //.addToContextNote("CSM");
    }

    static CsmElement token(int tokenType) {
        return new CsmToken(tokenType); //.addToContextNote("CSM");
    }

    static CsmElement token(int tokenType, CsmToken.TokenContentCalculator tokenContentCalculator) {
        return new CsmToken(tokenType, tokenContentCalculator); //.addToContextNote("CSM");
    }

    static CsmElement conditional(ObservableProperty property, CsmConditional.Condition condition, CsmElement thenElement) {
        return new CsmConditional(property, condition, thenElement); //.addToContextNote("CSM");
    }

    static CsmElement conditional(ObservableProperty property, CsmConditional.Condition condition, CsmElement thenElement, CsmElement elseElement) {
        return new CsmConditional(property, condition, thenElement, elseElement); //.addToContextNote("CSM");
    }

    static CsmElement conditional(List<ObservableProperty> properties, CsmConditional.Condition condition, CsmElement thenElement, CsmElement elseElement) {
        return new CsmConditional(properties, condition, thenElement, elseElement); //.addToContextNote("CSM");
    }

    static CsmElement space() {
        return new CsmToken(spaceTokenKind(), " "); //.addToContextNote("CSM");
    }

    static CsmElement semicolon() {
        return new CsmToken(GeneratedJavaParserConstants.SEMICOLON); //.addToContextNote("CSM");
    }

    static CsmElement comment() {
        return new CsmComment(); //.addToContextNote("CSM");
    }

    static CsmElement newline() {
        return newline(LineSeparator.SYSTEM); //.addToContextNote("; CSM (system line separator)");
    }

    static CsmElement newline(LineSeparator lineSeparator) {
        return new CsmToken(eolTokenKind(lineSeparator), lineSeparator.asRawString()); //.addToContextNote("CSM (given line separator)");
    }

    static CsmElement none() {
        return new CsmNone(); //.addToContextNote("CSM");
    }

    static CsmElement comma() {
        return new CsmToken(GeneratedJavaParserConstants.COMMA); //.addToContextNote("CSM");
    }

    static CsmElement list(ObservableProperty property) {
        return new CsmList(property); //.addToContextNote("CSM");
    }

    static CsmElement list(ObservableProperty property, CsmElement separator) {
        return new CsmList(property, CsmElement.none(), separator, new CsmNone(), new CsmNone()); //.addToContextNote("CSM");
    }

    static CsmElement list(ObservableProperty property, CsmElement separator, CsmElement preceeding, CsmElement following) {
        return new CsmList(property, none(), separator, preceeding, following); //.addToContextNote("CSM");
    }

    static CsmElement list(ObservableProperty property, CsmElement separatorPre, CsmElement separatorPost, CsmElement preceeding, CsmElement following) {
        return new CsmList(property, separatorPre, separatorPost, preceeding, following); //.addToContextNote("CSM");
    }

    static CsmElement orphanCommentsEnding() {
        return new CsmOrphanCommentsEnding(); //.addToContextNote("CSM");
    }

    static CsmElement orphanCommentsBeforeThis() {
        // FIXME
        return new CsmNone(); //.addToContextNote("CSM");
    }

    static CsmElement indent() {
        return new CsmIndent(); //.addToContextNote("CSM");
    }

    static CsmElement unindent() {
        return new CsmUnindent(); //.addToContextNote("CSM");
    }

    static CsmElement block(CsmElement content) {
        return sequence(token(GeneratedJavaParserConstants.LBRACE), indented(content), token(GeneratedJavaParserConstants.RBRACE));
    }

    static CsmElement bracketed(CsmElement content) {
        return sequence(token(GeneratedJavaParserConstants.LPAREN), content, token(GeneratedJavaParserConstants.RPAREN));
    }

    static CsmElement indented(CsmElement content) {
        return sequence(indent(), content, unindent());
    }
}
