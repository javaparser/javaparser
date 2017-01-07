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

import java.util.LinkedList;
import java.util.List;

/**
 * A text, potentially containing tags.
 */
public class JavadocText {

    private List<JavadocTextElement> elements;

    public static JavadocText fromText(String text) {
        JavadocText instance = new JavadocText();
        instance.addElement(new JavadocSnippet(text));
        return instance;
    }

    public JavadocText() {
        elements = new LinkedList<>();
    }

    public void addElement(JavadocTextElement element) {
        this.elements.add(element);
    }

    public String toText() {
        StringBuffer sb = new StringBuffer();
        elements.forEach(e -> sb.append(e.toText()));
        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavadocText that = (JavadocText) o;

        return elements.equals(that.elements);

    }

    @Override
    public int hashCode() {
        return elements.hashCode();
    }
}
