/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

package com.github.javaparser.printer;

import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.Test;

/**
 * Comment content set programmatically must stay inside the comment when printed.
 */
class CommentContentPrintingTest {

    private static final String CLOSING = "text */ static { System.exit(1); } /* more";

    private static final String NEWLINE = "text\nstatic { System.exit(1); }";

    private static void assertNoCodeInjected(String printed) {
        CompilationUnit reparsed = StaticJavaParser.parse(printed);
        assertTrue(reparsed.findAll(InitializerDeclaration.class).isEmpty(), printed);
    }

    @Test
    void prettyPrinterKeepsClosingSequenceInsideComments() {
        CompilationUnit cu = new CompilationUnit();
        ClassOrInterfaceDeclaration type = cu.addClass("A");
        type.addMethod("m").setJavadocComment(CLOSING);
        type.addField("int", "f").setComment(new BlockComment(CLOSING));

        String printed = cu.toString();

        assertNoCodeInjected(printed);
        assertTrue(printed.contains("text *&#47; static { System.exit(1); } /* more"), printed);
    }

    @Test
    void lexicalPreservingPrinterKeepsClosingSequenceInsideComments() {
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse("class A { void m() {} int f; }"));
        cu.findFirst(MethodDeclaration.class).get().setJavadocComment(CLOSING);
        cu.getClassByName("A").get().getFieldByName("f").get().setComment(new BlockComment(CLOSING));

        assertNoCodeInjected(LexicalPreservingPrinter.print(cu));
    }

    @Test
    void lexicalPreservingPrinterKeepsLineBreaksOutOfLineComments() {
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse("class A { int f; }"));
        cu.getClassByName("A").get().getFieldByName("f").get().setComment(new LineComment(NEWLINE));

        assertNoCodeInjected(LexicalPreservingPrinter.print(cu));
    }

    @Test
    void lexicalPreservingPrinterKeepsClosingSequenceInsideCommentsOfNewNodes() {
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse("class A { }"));
        cu.getClassByName("A").get().addMethod("m").setJavadocComment(CLOSING);
        cu.getClassByName("A").get().addField("int", "f").setComment(new LineComment(NEWLINE));

        assertNoCodeInjected(LexicalPreservingPrinter.print(cu));
    }
}
