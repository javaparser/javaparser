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

package com.github.javaparser.javadoc;

import com.github.javaparser.javadoc.description.JavadocDescription;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.nextWord;
import static com.github.javaparser.utils.Utils.screamingToCamelCase;

/**
 * A block tag.
 * <p>
 * Typically they are found at the end of Javadoc comments.
 * <p>
 * Examples:
 * <code>@see AnotherClass</code>
 * <code>@since v0.0.1</code>
 * <code>@author Jim O'Java</code>
 */
public class JavadocBlockTag {

    /**
     * The type of tag: it could either correspond to a known tag (param, return, etc.) or represent
     * an unknown tag.
     */
    public enum Type {
        AUTHOR,
        DEPRECATED,
        EXCEPTION,
        PARAM,
        RETURN,
        SEE,
        SERIAL,
        SERIAL_DATA,
        SERIAL_FIELD,
        SINCE,
        THROWS,
        VERSION,
        UNKNOWN;

        Type() {
            this.keyword = screamingToCamelCase(name());
        }

        private String keyword;

        boolean hasName() {
            return this == PARAM;
        }

        static Type fromName(String tagName) {
            for (Type t : Type.values()) {
                if (t.keyword.equals(tagName)) {
                    return t;
                }
            }
            return UNKNOWN;
        }

    }

    private Type type;
    private JavadocDescription content;
    private Optional<String> name = Optional.empty();
    private String tagName;

    public JavadocBlockTag(Type type, String content) {
        this.type = type;
        this.tagName = type.keyword;
        if (type.hasName()) {
            this.name = Optional.of(nextWord(content));
            content = content.substring(this.name.get().length()).trim();
        }
        this.content = JavadocDescription.parseText(content);
    }

    public JavadocBlockTag(String tagName, String content) {
        this(Type.fromName(tagName), content);
        this.tagName = tagName;
    }

    public static JavadocBlockTag createParamBlockTag(String paramName, String content) {
        return new JavadocBlockTag(Type.PARAM, paramName + " " + content);
    }

    public Type getType() {
        return type;
    }

    public JavadocDescription getContent() {
        return content;
    }

    public Optional<String> getName() {
        return name;
    }

    public String getTagName() {
        return tagName;
    }

    public String toText() {
        StringBuilder sb = new StringBuilder();
        sb.append("@");
        sb.append(tagName);
        name.ifPresent(s -> sb.append(" ").append(s));
        if (!content.isEmpty()) {
            sb.append(" ");
            sb.append(content.toText());
        }
        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavadocBlockTag that = (JavadocBlockTag) o;

        if (type != that.type) return false;
        if (!content.equals(that.content)) return false;
        return name.equals(that.name);
    }

    @Override
    public int hashCode() {
        int result = type.hashCode();
        result = 31 * result + content.hashCode();
        result = 31 * result + name.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "JavadocBlockTag{" +
                "type=" + type +
                ", content='" + content + '\'' +
                ", name=" + name +
                '}';
    }
}
