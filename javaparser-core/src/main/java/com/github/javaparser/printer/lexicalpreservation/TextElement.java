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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Node;

public abstract class TextElement implements TextElementMatcher {

    abstract String expand();

    abstract boolean isToken(int tokenKind);

    final boolean isCommentToken() {
        return isToken(GeneratedJavaParserConstants.JAVADOC_COMMENT)
                || isToken(GeneratedJavaParserConstants.SINGLE_LINE_COMMENT)
                || isToken(GeneratedJavaParserConstants.MULTI_LINE_COMMENT);
    }

    @Override
    public boolean match(TextElement textElement) {
        return this.equals(textElement);
    }

    abstract boolean isNode(Node node);

    public abstract boolean isWhiteSpace();

    public abstract boolean isSpaceOrTab();

    public abstract boolean isNewline();

    public abstract boolean isComment();

    public final boolean isWhiteSpaceOrComment() {
        return isWhiteSpace() || isComment();
    }

    /**
     * Is this TextElement representing a child of the given class?
     */
    public abstract boolean isChildOfClass(Class<? extends Node> nodeClass);
}
