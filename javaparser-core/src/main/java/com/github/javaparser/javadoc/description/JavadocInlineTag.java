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

import com.github.javaparser.javadoc.JavadocParser;
import com.github.javaparser.utils.Utils;

/**
 * An inline tag contained in a Javadoc description.
 * <p>
 * For example <code>{@link String}</code>
 */
public class JavadocInlineTag implements JavadocDescriptionElement {

    public static JavadocDescriptionElement fromText(String text) {
        if (!text.startsWith("{@")) {
            throw new IllegalArgumentException(String.format("Expected to start with '{@'. Text '%s'", text));
        }
        if (!text.endsWith("}")) {
            throw new IllegalArgumentException(String.format("Expected to end with '}'. Text '%s'", text));
        }
        text = text.substring(2, text.length() - 1);
        String tagName = JavadocParser.nextWord(text);
        Type type = Type.fromName(tagName);
        String content = text.substring(tagName.length());
        return new JavadocInlineTag(type, content);
    }

    /**
     * The type of tag: it could either correspond to a known tag (code, docRoot, etc.) or represent
     * an unknown tag.
     */
    public enum Type {
        CODE,
        DOC_ROOT,
        INHERIT_DOC,
        LINK,
        LINKPLAIN,
        LITERAL,
        VALUE,
        UNKNOWN;

        Type() {
            this.keyword = Utils.toCamelCase(name());
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

    private Type type;
    private String content;

    public JavadocInlineTag(Type type, String content) {
        this.type = type;
        this.content = content;
    }

    @Override
    public String toText() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavadocInlineTag that = (JavadocInlineTag) o;

        if (type != that.type) return false;
        return content.equals(that.content);

    }

    @Override
    public int hashCode() {
        int result = type.hashCode();
        result = 31 * result + content.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "JavadocInlineTag{" +
                "type=" + type +
                ", content='" + content + '\'' +
                '}';
    }
}
