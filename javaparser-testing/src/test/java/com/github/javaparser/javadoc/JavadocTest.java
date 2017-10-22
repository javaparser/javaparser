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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.javadoc.description.JavadocDescription;
import org.junit.jupiter.api.Test;

import java.io.FileNotFoundException;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class JavadocTest {

    @Test
    public void toTextForEmptyJavadoc() throws FileNotFoundException {
        Javadoc javadoc = new Javadoc(new JavadocDescription());
        assertEquals("", javadoc.toText());
    }

    @Test
    public void toTextForJavadocWithTwoLinesOfJustDescription() throws FileNotFoundException {
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("first line\nsecond line"));
        assertEquals("first line\nsecond line\n", javadoc.toText());
    }

    @Test
    public void toTextForJavadocWithTwoLinesOfJustDescriptionAndOneBlockTag() throws FileNotFoundException {
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("first line\nsecond line"));
        javadoc.addBlockTag("foo", "something useful");
        assertEquals("first line\nsecond line\n\n@foo something useful\n", javadoc.toText());
    }

    @Test
    public void toCommentForEmptyJavadoc() throws FileNotFoundException {
        Javadoc javadoc = new Javadoc(new JavadocDescription());
        assertEquals(new JavadocComment("\n\t\t "), javadoc.toComment("\t\t"));
    }

    @Test
    public void toCommentorJavadocWithTwoLinesOfJustDescription() throws FileNotFoundException {
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("first line\nsecond line"));
        assertEquals(new JavadocComment("\n\t\t * first line\n\t\t * second line\n\t\t "), javadoc.toComment("\t\t"));
    }

    @Test
    public void toCommentForJavadocWithTwoLinesOfJustDescriptionAndOneBlockTag() throws FileNotFoundException {
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("first line\nsecond line"));
        javadoc.addBlockTag("foo", "something useful");
        assertEquals(new JavadocComment("\n\t\t * first line\n\t\t * second line\n\t\t * \n\t\t * @foo something useful\n\t\t "), javadoc.toComment("\t\t"));
    }

    @Test
    public void descriptionAndBlockTagsAreRetrievable() {
        Javadoc javadoc = JavaParser.parseJavadoc("first line\nsecond line\n\n@param node a node\n@return result the result");
        assertEquals(javadoc.getDescription().toText(), "first line\nsecond line");
        assertEquals(javadoc.getBlockTags().size(), 2);
    }

    @Test
    public void inlineTagsAreParsable() {
        String docText =
                "Returns the {@link TOFilename}s of all files that existed during the requested\n" +
                        "{@link TOVersion}.\n" +
                        "\n" +
                        "@param versionID the id of the {@link TOVersion}.\n" +
                        "@return the filenames\n" +
                        "@throws InvalidIDException if the {@link IPersistence} doesn't recognize the given versionID.\n";
        String javadoc = JavaParser.parseJavadoc(docText).toText();
        assertEquals(true, javadoc.contains("{@link TOVersion}"));
    }

    @Test
    public void emptyLinesBetweenBlockTagsGetsFiltered() {
        String comment = " * The type of the Object to be mapped.\n" +
                " * This interface maps the given Objects to existing ones in the database and\n" +
                " * saves them.\n" +
                " * \n" +
                " * @author censored\n" +
                " * \n" +
                " * @param <T>\n";
        Javadoc javadoc = JavaParser.parseJavadoc(comment);
        assertEquals(javadoc.getBlockTags().size(), 2);
    }

}
