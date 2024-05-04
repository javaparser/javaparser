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

package com.github.javaparser.ast;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.utils.LineSeparator;

class NodeTest {
    @Test
    void removeOrphanCommentPositiveCase() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "A");
        Comment c = new LineComment("A comment");
        decl.addOrphanComment(c);
        assertEquals(1, decl.getOrphanComments().size());
        assertSame(decl, c.getParentNode().get());
        assertTrue(decl.removeOrphanComment(c));
        assertEquals(0, decl.getOrphanComments().size());
        assertFalse(c.getParentNode().isPresent());
    }

    @Test
    void removeOrphanCommentNegativeCase() {
        ClassOrInterfaceDeclaration aClass = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "A");
        FieldDeclaration aField = new FieldDeclaration(new NodeList<>(), new VariableDeclarator(PrimitiveType.intType(), "f"));
        aClass.getMembers().add(aField);
        Comment c = new LineComment("A comment");
        aField.addOrphanComment(c);
        // the comment is an orphan comment of the field, so trying to remove it on the class should not work
        assertFalse(aClass.removeOrphanComment(c));
        assertEquals(1, aField.getOrphanComments().size());
        assertTrue(c.getParentNode().isPresent());
    }

    @Test
    void hasJavaDocCommentPositiveCaseWithSetJavaDocComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "Foo");
        decl.setJavadocComment("A comment");
        assertTrue(decl.hasJavaDocComment());
    }

    @Test
    void hasJavaDocCommentPositiveCaseWithSetComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "Foo");
        decl.setComment(new JavadocComment("A comment"));
        assertTrue(decl.hasJavaDocComment());
    }

    @Test
    void hasJavaDocCommentNegativeCaseNoComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "Foo");
        assertFalse(decl.hasJavaDocComment());
    }

    @Test
    void hasJavaDocCommentNegativeCaseLineComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "Foo");
        decl.setComment(new LineComment("foo"));
        assertFalse(decl.hasJavaDocComment());
    }

    @Test
    void hasJavaDocCommentNegativeCaseBlockComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "Foo");
        decl.setComment(new BlockComment("foo"));
        assertFalse(decl.hasJavaDocComment());
    }

    @Test
    void findCompilationUnitOfCommentNode() {
        CompilationUnit cu = parse("class X {\n" +
                "  void x() {\n" +
                "    // this is a comment\n" +
                "    foo();\n" +
                "  }\n" +
                "}\n");

        Comment comment = cu.getType(0).getMember(0)
                .asMethodDeclaration().getBody().get()
                .getStatement(0).getComment().get();

        assertTrue(comment.findCompilationUnit().isPresent());
    }

    @Test
    void findCompilationUnitOfOrphanCommentNode() {
        CompilationUnit cu = parse("class X {\n" +
                "  void x() {\n" +
                "    // this is a comment\n" +
                "  }\n" +
                "}\n");

        Comment comment = cu.getType(0).getMember(0)
                .asMethodDeclaration().getBody().get()
                .getOrphanComments().get(0);

        assertTrue(comment.findCompilationUnit().isPresent());
    }

    @Test
    void removeAllOnRequiredProperty() {
        CompilationUnit cu = parse("class X{ void x(){}}");
        MethodDeclaration methodDeclaration = cu.getType(0).getMethods().get(0);
        methodDeclaration.getName().removeForced();
        // Name is required, so to remove it the whole method is removed.
        assertEquals(String.format("class X {%1$s}%1$s", LineSeparator.SYSTEM), cu.toString());
    }

    @Test
    void removingTheSecondOfAListOfIdenticalStatementsDoesNotMessUpTheParents() {
        CompilationUnit unit = parse(String.format("public class Example {%1$s" +
                "  public static void example() {%1$s" +
                "    boolean swapped;%1$s" +
                "    swapped=false;%1$s" +
                "    swapped=false;%1$s" +
                "  }%1$s" +
                "}%1$s", LineSeparator.SYSTEM));
        // remove the second swapped=false
        ExpressionStmt target = unit.findAll(ExpressionStmt.class).get(2);
        target.remove();
        // This will throw an exception if the parents are bad.
        unit.toString();
    }

    @Test
    void findNodeByRange() {
        CompilationUnit cu = parse("class X {\n" +
                "  void x() {\n" +
                "  }\n" +
                "}\n");
        ClassOrInterfaceDeclaration coid = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
        MethodDeclaration md = cu.findFirst(MethodDeclaration.class).get();

        // The range corresponds to the compilation unit
        Optional<Node> node = cu.findByRange(new Range(new Position(1,1), new Position(4,2)));
        assertTrue(node.isPresent());
        assertEquals(cu, node.get());

        // The range corresponds to the class declaration
        node = cu.findByRange(new Range(new Position(1,1), new Position(4,1)));
        assertTrue(node.isPresent());
        assertEquals(coid, node.get());

        // The range corresponds to the method declaration
        node = cu.findByRange(new Range(new Position(2,3), new Position(3,3)));
        assertTrue(node.isPresent());
        assertEquals(md, node.get());

        // The range is included in the class declaration
        node = cu.findByRange(new Range(new Position(1,1), new Position(1,1)));
        assertTrue(node.isPresent());
        assertEquals(coid, node.get());

        // The range is not included in the compilation unit
        node = cu.findByRange(new Range(new Position(5,1), new Position(5,1)));
        assertFalse(node.isPresent());

        // Search based on the method declaration, but the range corresponds to a parent node.
        node = md.findByRange(new Range(new Position(1,1), new Position(1,1)));
        assertFalse(node.isPresent());
    }
}
