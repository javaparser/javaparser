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

public class JavadocBlockTag {
    public enum Type {
        PARAM,
        RETURN,
        UNKNOWN;

        static Type fromName(String tagName) {
            for (Type t : Type.values()) {
                if (t.name().toLowerCase().equals(tagName)) {
                    return t;
                }
            }
            return UNKNOWN;
        }

    }

    private Type type;
    private String content;

    public JavadocBlockTag(Type type, String content) {
        this.type = type;
        this.content = content;
    }

    public JavadocBlockTag(String tagName, String content) {
        this(Type.fromName(tagName), content);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavadocBlockTag that = (JavadocBlockTag) o;

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
        return "JavadocBlockTag{" +
                "type=" + type +
                ", content='" + content + '\'' +
                '}';
    }
}
