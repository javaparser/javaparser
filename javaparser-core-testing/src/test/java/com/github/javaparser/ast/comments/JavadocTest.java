/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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
package com.github.javaparser.ast.comments;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.JavadocDescriptionElement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.Utils.EOL;
import com.github.javaparser.printer.PrettyPrinterConfiguration;

import java.util.List;

import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static java.util.stream.Collectors.toList;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for JavaDoc parsing.
 */
class JavadocTest { 

    private static final PrettyPrinterConfiguration PRETTY_PRINTER_CONFIG_TWO_INDENT = new PrettyPrinterConfiguration().setIndentSize(2);

    @Test
    void toTextForEmptyJavadoc() {
        // REQ 2
        JavadocContent doc = new JavadocContent();
        assertEquals("", doc.toText());
    }

    @Test
    void toTextForJavadocWithTwoLinesOfJustDescription() {
        // REQ 2
        JavadocSnippet snippet = new JavadocSnippet("first line" + EOL + "second line");
        JavadocDescription description = new JavadocDescription(new NodeList<JavadocDescriptionElement>().addFirst(snippet));
        JavadocContent javadoc = new JavadocContent(description, new NodeList<JavadocBlockTag>());
        assertEquals("first line" + EOL + "second line" + EOL, javadoc.toText());
    }

    @Test
    void toTextForJavadocWithTwoLinesOfJustDescriptionAndOneBlockTag() {
        // REQ 2
        JavadocSnippet snippet = new JavadocSnippet("first line" + EOL + "second line");
        JavadocDescription description = new JavadocDescription(new NodeList<JavadocDescriptionElement>().addFirst(snippet));

        JavadocSnippet snippet2 = new JavadocSnippet("something useful");
        NodeList<JavadocDescriptionElement> elements2 = new NodeList<JavadocDescriptionElement>().addFirst(snippet2);

        JavadocDescription tagDescription = new JavadocDescription(elements2);
        JavadocBlockTag tag = new JavadocBlockTag(tagDescription, JavadocBlockTag.BlockTagType.AUTHOR);

        NodeList<JavadocBlockTag> tags = new NodeList<JavadocBlockTag>().addLast(tag);
        JavadocContent javadoc = new JavadocContent("", description, tags);
        assertEquals("first line" + EOL + "second line" + EOL + EOL + "@author something useful" + EOL, javadoc.toText());
    }

//    @Test
//    void descriptionAndBlockTagsAreRetrievable() {
//        // TODO: Test is more relevant to the grammar
//        // REQ 1 & 2
//        Javadoc javadoc = parseJavadoc("first line" + EOL + "second line" + EOL + EOL + "@param node a node" + EOL + "@return result the result");
//        assertEquals("first line" + EOL + "second line", javadoc.getDescription().toText());
//        assertEquals(2, javadoc.getBlockTags().size());
//    }


    // TODO: Add when inlineTags are added
//    @Test
//    void inlineTagsAreParsable() {
//    // REQ 1 & 2
//        String docText =
//          "Returns the {@link TOFilename}s of all files that existed during the requested" + EOL +
//            "{@link TOVersion}. Set {@systemProperty JAVA_HOME} correctly." + EOL +
//            "" + EOL +
//            "@param versionID the id of the {@link TOVersion}." + EOL +
//            "@return the filenames" + EOL +
//            "@throws InvalidIDException if the {@link IPersistence} doesn't recognize the given versionID." + EOL;
//        Javadoc javadoc = parseJavadoc(docText);
//
//        List<com.github.javaparser.javadoc.description.JavadocInlineTag> inlineTags = javadoc.getDescription().getElements().stream()
//          .filter(element -> element instanceof com.github.javaparser.javadoc.description.JavadocInlineTag)
//          .map(element -> (com.github.javaparser.javadoc.description.JavadocInlineTag) element)
//          .collect(toList());
//
//        assertEquals("link", inlineTags.get(0).getName());
//        assertEquals(" TOFilename", inlineTags.get(0).getContent());
//        assertEquals(LINK, inlineTags.get(0).getType());
//        assertEquals("link", inlineTags.get(1).getName());
//        assertEquals(" TOVersion", inlineTags.get(1).getContent());
//        assertEquals(LINK, inlineTags.get(1).getType());
//        assertEquals("systemProperty", inlineTags.get(2).getName());
//        assertEquals(" JAVA_HOME", inlineTags.get(2).getContent());
//        assertEquals(SYSTEM_PROPERTY, inlineTags.get(2).getType());
//
//        String javadocText = javadoc.toText();
//        assertTrue(javadocText.contains("{@link TOVersion}"));
//    }
//
    // TODO: Related to parsing
//    @Test
//    void emptyLinesBetweenBlockTagsGetsFiltered() {
//        // REQ 1
//        String comment = " * The type of the Object to be mapped." + EOL +
//          " * This interface maps the given Objects to existing ones in the database and" + EOL +
//          " * saves them." + EOL +
//          " * " + EOL +
//          " * @author censored" + EOL +
//          " * " + EOL +
//          " * @param <T>" + EOL;
//        Javadoc javadoc = parseJavadoc(comment);
//        assertEquals(2, javadoc.getBlockTags().size());
//    }
//

    @Test
    void blockTagModificationWorks() {
        // REQ 2
        JavadocContent javadoc = new JavadocContent(new JavadocDescription(), new NodeList<JavadocBlockTag>());

        assertEquals(0, javadoc.getBlockTags().size());
        JavadocDescription description = new JavadocDescription(new NodeList<JavadocDescriptionElement>().addFirst(new JavadocSnippet("a value")));
        JavadocBlockTag blockTag = new JavadocBlockTag(description, JavadocBlockTag.BlockTagType.RETURN);

        javadoc.getBlockTags().addFirst(blockTag);

        assertEquals(1, javadoc.getBlockTags().size());
        assertEquals(blockTag, javadoc.getBlockTags().get(0));

        assertEquals(blockTag, javadoc.getBlockTags().remove(0));
        assertEquals(0, javadoc.getBlockTags().size());
    }
    // TODO: Add when inline tags are added
//    @Test
//    void descriptionModificationWorks() {
//        // REQ 2
//        JavadocDescription description = new JavadocDescription();
//
//        assertEquals(0, description.getElements().size());
//
//        JavadocDescriptionElement inlineTag = new com.github.javaparser.javadoc.description.JavadocInlineTag("inheritDoc", INHERIT_DOC, "");
//        assertTrue(description.addElement(inlineTag));
//
//        assertEquals(1, description.getElements().size());
//        assertEquals(inlineTag, description.getElements().get(0));
//
//        assertEquals(inlineTag, description.getElements().remove(0));
//        assertEquals(0, description.getElements().size());
//    }
//
//    @Test
//    void issue1533() {
//        CompilationUnit compilationUnit = parse("/** hallo {@link Foo} welt */ public interface Foo extends Comparable { }");
//        List<JavadocDescriptionElement> elements = compilationUnit.getType(0).getJavadoc().get().getDescription().getElements();
//        assertEquals(3, elements.size());
//        assertEquals(new JavadocSnippet("hallo "), elements.get(0));
//        assertEquals(new JavadocInlineTag("link", LINK, " Foo"), elements.get(1));
//        assertEquals(new JavadocSnippet(" welt"), elements.get(2));
//    }
//

// I don't think the rest are related to our refactoring: They acts on the parent of a JavadocComment
}