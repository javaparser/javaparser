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

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.SourcePrinter;

import java.util.Arrays;


public interface CsmElement {

    void prettyPrint(Node node, SourcePrinter printer);

    static CsmElement child(ObservableProperty property) {
        return new CsmSingleReference(property);
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

    static CsmElement space() {
        return new CsmToken(32, " ");
    }

    static CsmElement semicolon() {
        return new CsmToken(ASTParserConstants.SEMICOLON);
    }

    static CsmElement newline() {
        return new CsmToken(3, "\n");
    }

    static CsmElement comma() {
        return new CsmToken(ASTParserConstants.COMMA);
    }

    static CsmElement child(Node child) {
        return (node, printer) -> genericPrettyPrint(child, printer);
    }

    static CsmElement list(ObservableProperty property) {
        return new CsmList(property);
    }

    static CsmElement list(ObservableProperty property, CsmElement separator, CsmElement preceeding, CsmElement following) {
        return new CsmList(property, separator, preceeding, following);
    }
}
