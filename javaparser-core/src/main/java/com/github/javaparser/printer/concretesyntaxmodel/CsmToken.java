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
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.SourcePrinter;


public class CsmToken implements CsmElement {
    private int tokenType;
    private String content;
    private ObservableProperty propertyContent;

    public CsmToken(int tokenType) {
        this.tokenType = tokenType;
        this.content = ASTParserConstants.tokenImage[tokenType];
        if (content.startsWith("\"")) {
            content = content.substring(1, content.length() - 1);
        }
    }

    public CsmToken(int tokenType, String content) {
        this.tokenType = tokenType;
        this.content = content;
    }

    public CsmToken(int tokenType, ObservableProperty content) {
        this.tokenType = tokenType;
        this.propertyContent = content;
    }

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        if (content != null) {
            printer.print(content);
        } else {
            printer.print(propertyContent.singleStringValueFor(node));
        }
    }
}
