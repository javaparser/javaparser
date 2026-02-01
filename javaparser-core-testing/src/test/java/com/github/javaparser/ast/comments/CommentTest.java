/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verifyNoInteractions;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.description.JavadocDescription;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.printer.configuration.Indentation;
import com.github.javaparser.printer.configuration.Indentation.IndentType;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.utils.LineSeparator;
import java.util.List;
import org.junit.jupiter.api.Test;

class CommentTest {

    private static final PrinterConfiguration PRETTY_PRINTER_CONFIG_TWO_INDENT = new DefaultPrinterConfiguration()
            .addOption(new DefaultConfigurationOption(ConfigOption.INDENTATION, new Indentation(IndentType.SPACES, 2)));

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
        CompilationUnit cu = parse("public class MyClass {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "  /**"
                + LineSeparator.SYSTEM + "   * Comment A"
                + LineSeparator.SYSTEM + "   */"
                + LineSeparator.SYSTEM + "  public void oneMethod() {"
                + LineSeparator.SYSTEM + "  }"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "  /**"
                + LineSeparator.SYSTEM + "   * Comment A"
                + LineSeparator.SYSTEM + "   */"
                + LineSeparator.SYSTEM + "  public void anotherMethod() {"
                + LineSeparator.SYSTEM + "  }"
                + LineSeparator.SYSTEM + "}"
                + LineSeparator.SYSTEM);

        MethodDeclaration methodDeclaration =
                cu.findFirst(MethodDeclaration.class).get();

        // Act
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("Change Javadoc"));
        methodDeclaration.setJavadocComment("", javadoc);

        // Assert
        assertEqualsStringIgnoringEol(
                "public class MyClass {\n" + "\n"
                        + "  /**\n"
                        + "   * Change Javadoc\n"
                        + "   */\n"
                        + "  public void oneMethod() {\n"
                        + "  }\n"
                        + "\n"
                        + "  /**\n"
                        + "   * Comment A\n"
                        + "   */\n"
                        + "  public void anotherMethod() {\n"
                        + "  }\n"
                        + "}\n",
                cu.toString(PRETTY_PRINTER_CONFIG_TWO_INDENT));
    }

    @Test
    void testRemoveDuplicateComment() {
        // Arrange
        CompilationUnit cu = parse("public class MyClass {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "  /**"
                + LineSeparator.SYSTEM + "   * Comment A"
                + LineSeparator.SYSTEM + "   */"
                + LineSeparator.SYSTEM + "  public void oneMethod() {"
                + LineSeparator.SYSTEM + "  }"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "  /**"
                + LineSeparator.SYSTEM + "   * Comment A"
                + LineSeparator.SYSTEM + "   */"
                + LineSeparator.SYSTEM + "  public void anotherMethod() {"
                + LineSeparator.SYSTEM + "  }"
                + LineSeparator.SYSTEM + "}"
                + LineSeparator.SYSTEM);

        MethodDeclaration methodDeclaration =
                cu.findFirst(MethodDeclaration.class).get();

        // Act
        methodDeclaration.removeComment();

        // Assert
        assertEqualsStringIgnoringEol(
                "public class MyClass {\n" + "\n"
                        + "  public void oneMethod() {\n"
                        + "  }\n"
                        + "\n"
                        + "  /**\n"
                        + "   * Comment A\n"
                        + "   */\n"
                        + "  public void anotherMethod() {\n"
                        + "  }\n"
                        + "}\n",
                cu.toString(PRETTY_PRINTER_CONFIG_TWO_INDENT));
    }

    @Test
    void testRemoveDuplicateJavaDocComment() {
        // Arrange
        CompilationUnit cu = parse("public class MyClass {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "  /**"
                + LineSeparator.SYSTEM + "   * Comment A"
                + LineSeparator.SYSTEM + "   */"
                + LineSeparator.SYSTEM + "  public void oneMethod() {"
                + LineSeparator.SYSTEM + "  }"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "  /**"
                + LineSeparator.SYSTEM + "   * Comment A"
                + LineSeparator.SYSTEM + "   */"
                + LineSeparator.SYSTEM + "  public void anotherMethod() {"
                + LineSeparator.SYSTEM + "  }"
                + LineSeparator.SYSTEM + "}"
                + LineSeparator.SYSTEM);

        MethodDeclaration methodDeclaration =
                cu.findAll(MethodDeclaration.class).get(1);

        // Act
        methodDeclaration.removeJavaDocComment();

        // Assert
        assertEqualsStringIgnoringEol(
                "public class MyClass {\n" + "\n"
                        + "  /**\n"
                        + "   * Comment A\n"
                        + "   */\n"
                        + "  public void oneMethod() {\n"
                        + "  }\n"
                        + "\n"
                        + "  public void anotherMethod() {\n"
                        + "  }\n"
                        + "}\n",
                cu.toString(PRETTY_PRINTER_CONFIG_TWO_INDENT));
    }

    @Test()
    void testVerifyOrphanCommentInsertedInEmptyBlock() {
        BlockStmt block = new BlockStmt();
        block.addOrphanComment(new LineComment("TODO"));
        assertTrue(block.toString().contains("TODO"));
    }

    @Test
    void issue4791Test() {
        String a = new String("Hello World");
        String b = new String("Hello World");
        LineComment comment = new LineComment(a);

        AstObserver observer = mock(AstObserver.class);
        comment.register(observer);

        comment.setContent(b);

        verifyNoInteractions(observer);
    }

    @Test
    void testSingleLineCommentContent() {
        CompilationUnit cu = parse("class Test {\n" + "  // this is a single line comment\n"
                + "  // and so is this\n"
                + "  void test() {}\n"
                + "}");

        MethodDeclaration testMethod = cu.findFirst(MethodDeclaration.class).get();

        Comment secondComment = testMethod.getComment().get();

        assertEqualsStringIgnoringEol(" and so is this", secondComment.getContent());

        List<Comment> orphanComments = cu.findFirst(TypeDeclaration.class).get().getOrphanComments();
        assertEquals(1, orphanComments.size());
        assertEqualsStringIgnoringEol(
                " this is a single line comment", orphanComments.get(0).getContent());
    }

    @Test
    void testJavadocCommentContent() {
        String commentCode = "\n   * This is a regular {@code JavaDoc comment}\n   * @see some reference\n    ";
        CompilationUnit cu = parse("class Test {\n" + "  /**" + commentCode + "*/\n" + "  void test() {}\n" + "}");

        MethodDeclaration testMethod = cu.findFirst(MethodDeclaration.class).get();

        assertTrue(testMethod.getJavadocComment().isPresent());

        JavadocComment comment = testMethod.getJavadocComment().get();

        assertEqualsStringIgnoringEol(commentCode, comment.getContent());
    }

    @Test
    void testSingleMarkdownComment() {
        String commentCode = "  /// This is a markdown comment test. It should\n" + "  /// /**\n"
                + "  ///  * Handle multiline comments.\n"
                + "  ///  */\n"
                + "  ///  // and single line comments\n"
                + "  ///\n"
                + "  ///  and empty lines preceded by ///\n"
                + "  ///  without issues\n";
        CompilationUnit cu = parse("class Test {\n" + commentCode + "  void test() {}\n" + "}");

        MethodDeclaration testMethod = cu.findFirst(MethodDeclaration.class).get();

        assertTrue(testMethod.getComment().isPresent());
        assertInstanceOf(MarkdownComment.class, testMethod.getComment().get());

        MarkdownComment comment = testMethod.getComment().get().asMarkdownComment();

        String expectedContent = "This is a markdown comment test. It should\n" + "/**\n"
                + " * Handle multiline comments.\n"
                + " */\n"
                + " // and single line comments\n"
                + "\n"
                + " and empty lines preceded by ///\n"
                + " without issues";
        assertEquals(expectedContent, comment.getMarkdownContent());
    }

    @Test
    void testMultipleMarkdownComments() {
        String comment1Code = "  /// This is a markdown comment test. It should\n" + "  /// /**\n"
                + "  ///  * Handle multiline comments.\n"
                + "  ///  */\n"
                + "  /// // and single line comments\n";
        String comment2Code = "  ///\n" + "  /// and empty lines preceded by ///\n" + "  /// without issues\n";
        CompilationUnit cu = parse("class Test {\n" + comment1Code + "\n" + comment2Code + "  void test() {}\n" + "}");

        MethodDeclaration testMethod = cu.findFirst(MethodDeclaration.class).get();

        assertTrue(testMethod.getComment().isPresent());
        assertInstanceOf(MarkdownComment.class, testMethod.getComment().get());

        MarkdownComment comment = testMethod.getComment().get().asMarkdownComment();

        String comment2Expectation = "///\n" + "  /// and empty lines preceded by ///\n" + "  /// without issues\n";
        assertEqualsStringIgnoringEol(comment2Expectation, comment.asString());

        List<Comment> orphanComments = cu.findFirst(TypeDeclaration.class).get().getOrphanComments();

        assertEquals(1, orphanComments.size());
        assertInstanceOf(MarkdownComment.class, orphanComments.get(0));

        String comment1Expectation = "/// This is a markdown comment test. It should\n" + "  /// /**\n"
                + "  ///  * Handle multiline comments.\n"
                + "  ///  */\n"
                + "  /// // and single line comments\n";
        assertEqualsStringIgnoringEol(comment1Expectation, orphanComments.get(0).asString());
    }

    @Test
    void markdownCommentShouldNotHaveSingleLineContent() {
        CompilationUnit cu = parse(
                "class Test {\n" + "  /// this is a single-line markdown comment test\n" + "  void test() {}\n" + "}");

        MethodDeclaration testMethod = cu.findFirst(MethodDeclaration.class).get();

        assertTrue(testMethod.getComment().isPresent());
        assertInstanceOf(MarkdownComment.class, testMethod.getComment().get());

        MarkdownComment comment = testMethod.getComment().get().asMarkdownComment();

        assertEqualsStringIgnoringEol("/// this is a single-line markdown comment test", comment.getContent());
        assertEqualsStringIgnoringEol("this is a single-line markdown comment test", comment.getMarkdownContent());
        assertEqualsStringIgnoringEol("/// this is a single-line markdown comment test\n", comment.asString());
    }

    @Test
    void testSplitMarkdownComment1() {
        String commentCode = "  /// This is a markdown comment test. It should\n" + "  /// /**\n"
                + "  ///  * Handle multiline comments.\n"
                + "  ///  */\n"
                + "  // split by single line comments\n"
                + "  ///\n"
                + "  ///  and empty lines preceded by ///\n"
                + "  ///  without issues\n";
        CompilationUnit cu = parse("class Test {\n" + commentCode + "  void test() {}\n" + "}");

        MethodDeclaration testMethod = cu.findFirst(MethodDeclaration.class).get();

        assertTrue(testMethod.getComment().isPresent());
        assertTrue(testMethod.getJavadocComment().isPresent());
        assertInstanceOf(MarkdownComment.class, testMethod.getComment().get());

        MarkdownComment comment = testMethod.getComment().get().asMarkdownComment();

        String expectedMarkdownContent = "\n" + "and empty lines preceded by ///\n" + "without issues";
        assertEquals(expectedMarkdownContent, comment.getMarkdownContent());

        String expectedContent = "///\n  ///  and empty lines preceded by ///\n  ///  without issues";
        assertEquals(expectedContent, comment.getContent());

        List<Comment> orphanComments = cu.findFirst(TypeDeclaration.class).get().getOrphanComments();

        assertEquals(2, orphanComments.size());

        assertInstanceOf(MarkdownComment.class, orphanComments.get(0));
        String expectedFirstOrphanContent =
                "This is a markdown comment test. It should\n" + "/**\n" + " * Handle multiline comments.\n" + " */";
        assertEqualsStringIgnoringEol(
                expectedFirstOrphanContent,
                orphanComments.get(0).asMarkdownComment().getMarkdownContent());

        assertInstanceOf(LineComment.class, orphanComments.get(1));
        assertEqualsStringIgnoringEol(
                " split by single line comments", orphanComments.get(1).getContent());
    }

    @Test
    void testTraditionalJavadocComment() {
        CompilationUnit cu = parse("class Test {\n" + "  /**\n"
                + "   * This is a traditional javadoc comment\n"
                + "   */\n"
                + "  void test() {}\n"
                + "}");

        MethodDeclaration testMethod = cu.findFirst(MethodDeclaration.class).get();

        assertTrue(testMethod.getComment().isPresent());
        assertInstanceOf(
                TraditionalJavadocComment.class, testMethod.getComment().get());

        String expectedContent = "\n   * This is a traditional javadoc comment\n   ";
        assertEquals(expectedContent, testMethod.getComment().get().getContent());
    }
}
