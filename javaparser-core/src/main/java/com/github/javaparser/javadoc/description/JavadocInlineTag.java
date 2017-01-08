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

package com.github.javaparser.javadoc.description;

import com.github.javaparser.javadoc.JavadocBlockTag;

public class JavadocInlineTag implements JavadocDescriptionElement {

    /**
     * The type of tag: it could either correspond to a known tag (code, docRoot, etc.) or represent
     * an unknown tag.
     */
    public enum Type {
        CODE,
        DOC_ROOT("docRoot"),
        INHERIT_DOC("inheritDoc"),
        LINK,
        LINKPLAIN,
        LITERAL,
        VALUE,
        UNKNOWN;

        Type(String keyword) {
            this.keyword = keyword;
        }

        Type() {
            this.keyword = name().toLowerCase();
        }

        private String keyword;

        static JavadocInlineTag.Type fromName(String tagName) {
            for (JavadocInlineTag.Type t : JavadocInlineTag.Type.values()) {
                if (t.keyword.equals(tagName)) {
                    return t;
                }
            }
            return UNKNOWN;
        }

    }

    @Override
    public String toText() {
        throw new UnsupportedOperationException();
    }
}
