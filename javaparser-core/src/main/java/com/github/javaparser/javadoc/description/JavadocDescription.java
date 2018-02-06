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

import com.github.javaparser.utils.Pair;

import java.util.LinkedList;
import java.util.List;

/**
 * A javadoc text, potentially containing inline tags.
 *
 * For example <code>This class is totally unrelated to {@link com.github.javaparser.Range}</code>
 */
public class JavadocDescription {

    private List<JavadocDescriptionElement> elements;

    public static JavadocDescription parseText(String text) {
        JavadocDescription instance = new JavadocDescription();
        int index = 0;
        Pair<Integer, Integer> nextInlineTagPos;
        while ((nextInlineTagPos = indexOfNextInlineTag(text, index)) != null) {
            if (nextInlineTagPos.a != index) {
                instance.addElement(new JavadocSnippet(text.substring(index, nextInlineTagPos.a + 1)));
            }
            instance.addElement(JavadocInlineTag.fromText(text.substring(nextInlineTagPos.a, nextInlineTagPos.b + 1)));
            index = nextInlineTagPos.b;
        }
        if (index < text.length()) {
            instance.addElement(new JavadocSnippet(text.substring(index)));
        }
        return instance;
    }

    private static Pair<Integer, Integer> indexOfNextInlineTag(String text, int start) {
        int index = text.indexOf("{@", start);
        if (index == -1) {
            return null;
        }
        // we are interested only in complete inline tags
        int closeIndex = text.indexOf("}", index);
        if (closeIndex == -1) {
            return null;
        }
        return new Pair<>(index, closeIndex);
    }

    public JavadocDescription() {
        elements = new LinkedList<>();
    }

    public JavadocDescription(List<JavadocDescriptionElement> elements) {
        this();

        this.elements.addAll(elements);
    }

    public boolean addElement(JavadocDescriptionElement element) {
        return this.elements.add(element);
    }

    public List<JavadocDescriptionElement> getElements() {
        return this.elements;
    }

    public String toText() {
        StringBuilder sb = new StringBuilder();
        elements.forEach(e -> sb.append(e.toText()));
        return sb.toString();
    }

    public boolean isEmpty() {
        return toText().isEmpty();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavadocDescription that = (JavadocDescription) o;

        return elements.equals(that.elements);

    }

    @Override
    public int hashCode() {
        return elements.hashCode();
    }

    @Override
    public String toString() {
        return "JavadocDescription{" +
                "elements=" + elements +
                '}';
    }

}
