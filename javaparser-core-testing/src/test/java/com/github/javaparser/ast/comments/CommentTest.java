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

package com.github.javaparser.ast.comments;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.description.JavadocDescription;
import com.github.javaparser.printer.PrettyPrinterConfiguration;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.*;

class CommentTest {

    private static final PrettyPrinterConfiguration PRETTY_PRINTER_CONFIG_TWO_INDENT = new PrettyPrinterConfiguration().setIndentSize(2);

    @Test
    void removeOrphanComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "A");
        Comment c = new LineComment("A comment");
        decl.addOrphanComment(c);
        assertEquals(1, decl.getOrphanComments().size());
        assertTrue(c.remove());
        assertEquals(0, decl.getOrphanComments().size());
    }

    @Test
    void removeAssociatedComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "A");
        Comment c = new LineComment("A comment");
        decl.setComment(c);
        assertTrue(decl.getComment().isPresent());
        assertTrue(c.remove());
        assertFalse(decl.getComment().isPresent());
    }

    @Test
    void cannotRemoveCommentNotUsedAnywhere() {
        Comment c = new LineComment("A comment");
        assertFalse(c.remove());
    }

    @Test
    void unicodeEscapesArePreservedInComments() {
        CompilationUnit cu = parse("// xxx\\u2122xxx");
        Comment comment = cu.getAllContainedComments().get(0);
        assertEquals(" xxx\\u2122xxx", comment.getContent());
    }

    @Test
    void testReplaceDuplicateJavaDocComment() {
        // Arrange
        CompilationUnit cu = parse("public class MyClass {" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void oneMethod() {" + EOL +
                "  }" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void anotherMethod() {" + EOL +
                "  }" + EOL +
                "}" + EOL);

        MethodDeclaration methodDeclaration = cu.findFirst(MethodDeclaration.class).get();

        // Act
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("Change Javadoc"));
        methodDeclaration.setJavadocComment("", javadoc);

        // Assert
        assertEqualsNoEol("public class MyClass {\n" +
                "\n" +
                "  /**\n" +
                "   * Change Javadoc\n" +
                "   */\n" +
                "  public void oneMethod() {\n" +
                "  }\n" +
                "\n" +
                "  /**\n" +
                "   * Comment A\n" +
                "   */\n" +
                "  public void anotherMethod() {\n" +
                "  }\n" +
                "}\n", cu.toString(PRETTY_PRINTER_CONFIG_TWO_INDENT));
    }

    @Test
    void testRemoveDuplicateComment() {
        // Arrange
        CompilationUnit cu = parse("public class MyClass {" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void oneMethod() {" + EOL +
                "  }" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void anotherMethod() {" + EOL +
                "  }" + EOL +
                "}" +
                EOL);

        MethodDeclaration methodDeclaration = cu.findFirst(MethodDeclaration.class).get();

        // Act
        methodDeclaration.removeComment();

        // Assert
        assertEqualsNoEol("public class MyClass {\n" +
                "\n" +
                "  public void oneMethod() {\n" +
                "  }\n" +
                "\n" +
                "  /**\n" +
                "   * Comment A\n" +
                "   */\n" +
                "  public void anotherMethod() {\n" +
                "  }\n" +
                "}\n", cu.toString(PRETTY_PRINTER_CONFIG_TWO_INDENT));
    }

    @Test
    void testRemoveDuplicateJavaDocComment() {
        // Arrange
        CompilationUnit cu = parse("public class MyClass {" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void oneMethod() {" + EOL +
                "  }" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void anotherMethod() {" + EOL +
                "  }" + EOL +
                "}" +
                EOL);

        MethodDeclaration methodDeclaration = cu.findAll(MethodDeclaration.class).get(1);

        // Act
        methodDeclaration.removeJavaDocComment();

        // Assert
        assertEqualsNoEol("public class MyClass {\n" +
                "\n" +
                "  /**\n" +
                "   * Comment A\n" +
                "   */\n" +
                "  public void oneMethod() {\n" +
                "  }\n" +
                "\n" +
                "  public void anotherMethod() {\n" +
                "  }\n" +
                "}\n", cu.toString(PRETTY_PRINTER_CONFIG_TWO_INDENT));
    }
}
