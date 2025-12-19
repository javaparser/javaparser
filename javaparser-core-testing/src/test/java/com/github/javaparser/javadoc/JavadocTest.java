/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseJavadoc;
import static com.github.javaparser.javadoc.description.JavadocInlineTag.Type.*;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static java.util.stream.Collectors.toList;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.TraditionalJavadocComment;
import com.github.javaparser.javadoc.description.JavadocDescription;
import com.github.javaparser.javadoc.description.JavadocDescriptionElement;
import com.github.javaparser.javadoc.description.JavadocInlineTag;
import com.github.javaparser.javadoc.description.JavadocSnippet;
import com.github.javaparser.utils.LineSeparator;
import java.util.List;
import org.junit.jupiter.api.Test;

class JavadocTest {

    @Test
    void toTextForEmptyJavadoc() {
        Javadoc javadoc = new Javadoc(new JavadocDescription());
        assertEquals("", javadoc.toText());
    }

    @Test
    void toTextForJavadocWithTwoLinesOfJustDescription() {
        Javadoc javadoc =
                new Javadoc(JavadocDescription.parseText("first line" + LineSeparator.SYSTEM + "second line"));
        assertEquals("first line" + LineSeparator.SYSTEM + "second line" + LineSeparator.SYSTEM, javadoc.toText());
    }

    @Test
    void toTextForJavadocWithTwoLinesOfJustDescriptionAndOneBlockTag() {
        Javadoc javadoc =
                new Javadoc(JavadocDescription.parseText("first line" + LineSeparator.SYSTEM + "second line"));
        javadoc.addBlockTag("foo", "something useful");
        assertEquals(
                "first line" + LineSeparator.SYSTEM + "second line" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "@foo something useful" + LineSeparator.SYSTEM,
                javadoc.toText());
    }

    @Test
    void toCommentForEmptyJavadoc() {
        Javadoc javadoc = new Javadoc(new JavadocDescription());
        assertEquals(new TraditionalJavadocComment("" + LineSeparator.SYSTEM + "\t\t "), javadoc.toComment("\t\t"));
    }

    @Test
    void toCommentorJavadocWithTwoLinesOfJustDescription() {
        Javadoc javadoc =
                new Javadoc(JavadocDescription.parseText("first line" + LineSeparator.SYSTEM + "second line"));
        assertEquals(
                new TraditionalJavadocComment("" + LineSeparator.SYSTEM + "\t\t * first line" + LineSeparator.SYSTEM
                        + "\t\t * second line" + LineSeparator.SYSTEM + "\t\t "),
                javadoc.toComment("\t\t"));
    }

    @Test
    void toCommentForJavadocWithTwoLinesOfJustDescriptionAndOneBlockTag() {
        Javadoc javadoc =
                new Javadoc(JavadocDescription.parseText("first line" + LineSeparator.SYSTEM + "second line"));
        javadoc.addBlockTag("foo", "something useful");
        assertEquals(
                new TraditionalJavadocComment("" + LineSeparator.SYSTEM + "\t\t * first line" + LineSeparator.SYSTEM
                        + "\t\t * second line" + LineSeparator.SYSTEM + "\t\t * " + LineSeparator.SYSTEM
                        + "\t\t * @foo something useful" + LineSeparator.SYSTEM + "\t\t "),
                javadoc.toComment("\t\t"));
    }

    @Test
    void descriptionAndBlockTagsAreRetrievable() {
        Javadoc javadoc = parseJavadoc(
                "first line" + LineSeparator.SYSTEM + "second line" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "@param node a node" + LineSeparator.SYSTEM + "@return result the result",
                false);
        assertEquals(
                "first line" + LineSeparator.SYSTEM + "second line",
                javadoc.getDescription().toText());
        assertEquals(2, javadoc.getBlockTags().size());
    }

    @Test
    void inlineTagsAreParsable() {
        String docText = "Returns the {@link TOFilename}s of all files that existed during the requested"
                + LineSeparator.SYSTEM + "{@link TOVersion}. Set {@systemProperty JAVA_HOME} correctly."
                + LineSeparator.SYSTEM + ""
                + LineSeparator.SYSTEM + "@param versionID the id of the {@link TOVersion}."
                + LineSeparator.SYSTEM + "@return the filenames"
                + LineSeparator.SYSTEM
                + "@throws InvalidIDException if the {@link IPersistence} doesn't recognize the given versionID."
                + LineSeparator.SYSTEM;
        Javadoc javadoc = parseJavadoc(docText, false);

        List<JavadocInlineTag> inlineTags = javadoc.getDescription().getElements().stream()
                .filter(element -> element instanceof JavadocInlineTag)
                .map(element -> (JavadocInlineTag) element)
                .collect(toList());

        assertEquals("link", inlineTags.get(0).getName());
        assertEquals(" TOFilename", inlineTags.get(0).getContent());
        assertEquals(LINK, inlineTags.get(0).getType());
        assertEquals("link", inlineTags.get(1).getName());
        assertEquals(" TOVersion", inlineTags.get(1).getContent());
        assertEquals(LINK, inlineTags.get(1).getType());
        assertEquals("systemProperty", inlineTags.get(2).getName());
        assertEquals(" JAVA_HOME", inlineTags.get(2).getContent());
        assertEquals(SYSTEM_PROPERTY, inlineTags.get(2).getType());

        String javadocText = javadoc.toText();
        assertTrue(javadocText.contains("{@link TOVersion}"));
    }

    @Test
    void emptyLinesBetweenBlockTagsGetsFiltered() {
        String comment = " * The type of the Object to be mapped." + LineSeparator.SYSTEM
                + " * This interface maps the given Objects to existing ones in the database and"
                + LineSeparator.SYSTEM + " * saves them."
                + LineSeparator.SYSTEM + " * "
                + LineSeparator.SYSTEM + " * @author censored"
                + LineSeparator.SYSTEM + " * "
                + LineSeparator.SYSTEM + " * @param <T>"
                + LineSeparator.SYSTEM;
        Javadoc javadoc = parseJavadoc(comment, false);
        assertEquals(2, javadoc.getBlockTags().size());
    }

    @Test
    void markdownJavadocParsed() {
        String comment = "/// The type of the Object to be mapped." + LineSeparator.SYSTEM
                + "    /// This interface maps the given Objects to existing ones in the database and"
                + LineSeparator.SYSTEM + "    /// saves them."
                + LineSeparator.SYSTEM + "    /// "
                + LineSeparator.SYSTEM + "    /// @author censored"
                + LineSeparator.SYSTEM + "    /// "
                + LineSeparator.SYSTEM + "    /// @param <T>"
                + LineSeparator.SYSTEM;
        Javadoc javadoc = parseJavadoc(comment, true);
        assertEqualsStringIgnoringEol(
                "The type of the Object to be mapped.\n"
                        + "This interface maps the given Objects to existing ones in the database and\n"
                        + "saves them.",
                javadoc.getDescription().toText());
        assertEquals(2, javadoc.getBlockTags().size());
        assertEquals("@author censored", javadoc.getBlockTags().get(0).toText());
        assertEquals("@param <T>", javadoc.getBlockTags().get(1).toText());
    }

    @Test
    void blockTagModificationWorks() {
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
    void descriptionModificationWorks() {
        JavadocDescription description = new JavadocDescription();

        assertEquals(0, description.getElements().size());

        JavadocDescriptionElement inlineTag = new JavadocInlineTag("inheritDoc", INHERIT_DOC, "");
        assertTrue(description.addElement(inlineTag));

        assertEquals(1, description.getElements().size());
        assertEquals(inlineTag, description.getElements().get(0));

        assertEquals(inlineTag, description.getElements().remove(0));
        assertEquals(0, description.getElements().size());
    }

    @Test
    void issue1533() {
        CompilationUnit compilationUnit =
                parse("/** hallo {@link Foo} welt */ public interface Foo extends Comparable { }");
        List<JavadocDescriptionElement> elements =
                compilationUnit.getType(0).getJavadoc().get().getDescription().getElements();
        assertEquals(3, elements.size());
        assertEquals(new JavadocSnippet("hallo "), elements.get(0));
        assertEquals(new JavadocInlineTag("link", LINK, " Foo"), elements.get(1));
        assertEquals(new JavadocSnippet(" welt"), elements.get(2));
    }
}
