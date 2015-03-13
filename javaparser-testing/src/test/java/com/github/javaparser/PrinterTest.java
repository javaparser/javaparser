/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.ModifierSet;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.lexical.Comment;
import com.github.javaparser.ast.lexical.CommentAttributes;
import com.github.javaparser.ast.lexical.CommentKind;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.utils.TestResources;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import java.io.*;

/**
 * @author Didier Villevalois
 */
@RunWith(JUnit4.class)
public class PrinterTest {

    private TestResources resources = new TestResources("com/github/javaparser/printer/", "");

    @Test
    public void parseDoNotPreserveAndFormat() throws ParseException, IOException {
        Assert.assertEquals(
                print(false, parse("Formatted.java", null, false, false)),
                print(true, parse("Formatted.java", null, false, true))
        );
    }

    @Test
    public void parsePreserveAndDoNotFormat() throws ParseException, IOException {
        Assert.assertEquals(
                resources.getResourceAsString("NonFormattedWithComments.java"),
                print(false, parse("NonFormattedWithComments.java", null, true, true))
        );
    }

    @Test
    public void addedContent() throws ParseException, IOException {
        CompilationUnit node = parse("NonFormattedWithComments.java", null, true, true);
        TypeDeclaration typeDeclaration = node.getTypes().get(0);

        BodyDeclaration method1 = typeDeclaration.getMembers().get(0);

        CommentAttributes method1Comments = method1.getCommentAttributes();
        method1Comments.getLeadingComments().add(0, new Comment(CommentKind.SINGLE_LINE, "// Cool 1"));
        method1Comments.getLeadingComments().add(new Comment(CommentKind.SINGLE_LINE, "// Cool 2"));
        method1Comments.getLeadingComments().add(new Comment(CommentKind.JAVA_DOC, "/** Doc addition */"));

        MethodDeclaration newMethod = new MethodDeclaration(
                ModifierSet.PUBLIC, new PrimitiveType(PrimitiveType.Primitive.Boolean), "newMethod"
        );
        typeDeclaration.getMembers().add(0, newMethod);

        CommentAttributes newMethodComments = new CommentAttributes();
        newMethod.setCommentAttributes(newMethodComments);
        newMethodComments.addLeadingComment(new Comment(CommentKind.JAVA_DOC, "/** New Method doc addition */"));

        Assert.assertEquals(
                resources.getResourceAsString("NonFormattedModified.java"),
                print(false, node));
        Assert.assertEquals(
                resources.getResourceAsString("NonFormattedModifiedAndFormatted.java"),
                print(true, node));
    }

    private CompilationUnit parse(String path, String encoding, boolean attributeComments, boolean preserveLexemes)
            throws ParseException, IOException {
        return JavaParser.parse(resources.getResourceAsStream(path), encoding, attributeComments, preserveLexemes);
    }

    private String print(boolean format, CompilationUnit node) {
        StringWriter writer = new StringWriter();
        Printer printer = new Printer(new PrintWriter(writer), format);
        printer.print(node);
        return writer.toString();
    }
}
