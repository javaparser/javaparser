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

import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.javadoc.description.JavadocDescription;

import java.util.LinkedList;
import java.util.List;

import static com.github.javaparser.utils.Utils.*;

/**
 * The structured content of a single Javadoc comment.
 * <p>
 * It is composed by a description and a list of block tags.
 * <p>
 * An example would be the text contained in this very Javadoc comment. At the moment
 * of this writing this comment does not contain any block tags (such as <code>@see AnotherClass</code>)
 */
public class Javadoc {

    private JavadocDescription description;
    private List<JavadocBlockTag> blockTags;

    public Javadoc(JavadocDescription description) {
        this.description = description;
        this.blockTags = new LinkedList<>();
    }

    public Javadoc addBlockTag(JavadocBlockTag blockTag) {
        this.blockTags.add(blockTag);
        return this;
    }

    public Javadoc addBlockTag(String tagName, String content) {
        return addBlockTag(new JavadocBlockTag(tagName, content));
    }

    public Javadoc addBlockTag(String tagName) {
        return addBlockTag(tagName, "");
    }

    /**
     * Return the text content of the document. It does not containing trailing spaces and asterisks
     * at the start of the line.
     */
    public String toText() {
        StringBuilder sb = new StringBuilder();
        if (!description.isEmpty()) {
            sb.append(description.toText());
            sb.append(EOL);
        }
        if (!blockTags.isEmpty()) {
            sb.append(EOL);
        }
        blockTags.forEach(bt -> {
            sb.append(bt.toText());
            sb.append(EOL);
        });
        return sb.toString();
    }

    /**
     * Create a JavadocComment, by formatting the text of the Javadoc using the given indentation/
     */
    public JavadocComment toComment(String indentation) {
        for (char c : indentation.toCharArray()) {
            if (!Character.isWhitespace(c)) {
                throw new IllegalArgumentException("The indentation string should be composed only by whitespace characters");
            }
        }
        StringBuilder sb = new StringBuilder();
        sb.append(EOL);
        final String text = toText();
        if (!text.isEmpty()) {
            for (String line : text.split(EOL)) {
                sb.append(indentation);
                sb.append(" * ");
                sb.append(line);
                sb.append(EOL);
            }
        }
        sb.append(indentation);
        sb.append(" ");
        return new JavadocComment(sb.toString());
    }

    public JavadocDescription getDescription() {
        return description;
    }

    /**
     * @return the current List of associated JavadocBlockTags
     */
    public List<JavadocBlockTag> getBlockTags() {
        return this.blockTags;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Javadoc document = (Javadoc) o;

        return description.equals(document.description) && blockTags.equals(document.blockTags);

    }

    @Override
    public int hashCode() {
        int result = description.hashCode();
        result = 31 * result + blockTags.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "Javadoc{" +
                "description=" + description +
                ", blockTags=" + blockTags +
                '}';
    }

}
