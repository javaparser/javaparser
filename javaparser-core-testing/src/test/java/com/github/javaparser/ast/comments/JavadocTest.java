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

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseMethodDeclaration;
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

//   @Test
//   void descriptionAndBlockTagsAreRetrievable() {
//       // REQ 1 & 2
//
//       CompilationUnit cu = parse("public class MyClass {" + EOL +
//         EOL +
//         "  /**" + EOL +
//         "   * first line" + EOL +
//         "   * second line" + EOL +
//         "   * @author Simon" + EOL +
//         "   * @return Nothing" + EOL +
//         "   */" + EOL +
//         "  public void oneMethod() {" + EOL +
//         "  }" + EOL +
//         "}" + EOL);
//
//       MethodDeclaration methodDeclaration = cu.findFirst(MethodDeclaration.class).get();
//       assertEquals("first line" + EOL + "second line", methodDeclaration.getJavadocComment().get().getContentNode().getDescription().toText());
//       assertEquals(2, methodDeclaration.getJavadocComment().get().getContentNode().getBlockTags().size());
//   }

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
}