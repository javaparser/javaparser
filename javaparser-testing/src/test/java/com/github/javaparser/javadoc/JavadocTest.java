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
import com.github.javaparser.javadoc.description.JavadocDescriptionElement;
import com.github.javaparser.javadoc.description.JavadocInlineTag;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class JavadocTest {

    @Test
    public void toTextForEmptyJavadoc() {
        Javadoc javadoc = new Javadoc(new JavadocDescription());
        assertEquals("", javadoc.toText());
    }

    @Test
    public void toTextForJavadocWithTwoLinesOfJustDescription() {
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("first line\nsecond line"));
        assertEquals("first line\nsecond line\n", javadoc.toText());
    }

    @Test
    public void toTextForJavadocWithTwoLinesOfJustDescriptionAndOneBlockTag() {
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("first line\nsecond line"));
        javadoc.addBlockTag("foo", "something useful");
        assertEquals("first line\nsecond line\n\n@foo something useful\n", javadoc.toText());
    }

    @Test
    public void toCommentForEmptyJavadoc() {
        Javadoc javadoc = new Javadoc(new JavadocDescription());
        assertEquals(new JavadocComment("\n\t\t "), javadoc.toComment("\t\t"));
    }

    @Test
    public void toCommentorJavadocWithTwoLinesOfJustDescription() {
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("first line\nsecond line"));
        assertEquals(new JavadocComment("\n\t\t * first line\n\t\t * second line\n\t\t "), javadoc.toComment("\t\t"));
    }

    @Test
    public void toCommentForJavadocWithTwoLinesOfJustDescriptionAndOneBlockTag() {
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("first line\nsecond line"));
        javadoc.addBlockTag("foo", "something useful");
        assertEquals(new JavadocComment("\n\t\t * first line\n\t\t * second line\n\t\t * \n\t\t * @foo something useful\n\t\t "), javadoc.toComment("\t\t"));
    }

    @Test
    public void descriptionAndBlockTagsAreRetrievable() {
        Javadoc javadoc = JavaParser.parseJavadoc("first line\nsecond line\n\n@param node a node\n@return result the result");
        assertEquals("first line\nsecond line", javadoc.getDescription().toText());
        assertEquals(2, javadoc.getBlockTags().size());
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
        assertTrue(javadoc.contains("{@link TOVersion}"));
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
        assertEquals(2, javadoc.getBlockTags().size());
    }

    @Test
    public void blockTagModificationWorks() {
        Javadoc javadoc = new Javadoc(new JavadocDescription());

        assertEquals(0, javadoc.getBlockTags().size());
        JavadocBlockTag blockTag = new JavadocBlockTag(JavadocBlockTag.Type.RETURN, "a value");
        javadoc.addBlockTag(blockTag);

        assertEquals(1, javadoc.getBlockTags().size());
        assertEquals(blockTag, javadoc.getBlockTags().get(0));

        assertEquals(blockTag, javadoc.getBlockTags().remove(0));
        assertEquals(0, javadoc.getBlockTags().size());
    }

    @Test
    public void descriptionModificationWorks() {
        JavadocDescription description = new JavadocDescription();

        assertEquals(0, description.getElements().size());

        JavadocDescriptionElement inlineTag = new JavadocInlineTag("inheritDoc", JavadocInlineTag.Type.INHERIT_DOC, "");
        assertTrue(description.addElement(inlineTag));

        assertEquals(1, description.getElements().size());
        assertEquals(inlineTag, description.getElements().get(0));

        assertEquals(inlineTag, description.getElements().remove(0));
        assertEquals(0, description.getElements().size());
    }

}
