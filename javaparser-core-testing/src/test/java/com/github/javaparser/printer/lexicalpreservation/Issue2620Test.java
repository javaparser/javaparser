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

package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Arrays;
import java.util.Optional;
import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

public class Issue2620Test {
    
    /*
     * This test case must prevent an UnsupportedOperation Removed throwed by LexicalPreservation when we try to replace an expression
     */
    @Test
    public void test() {
        String expected = 
                "public class Foo { //comment\n" +
                "  private String b;\n" +
                "  private String a;\n" +
                "}\n";
      
        CompilationUnit cu = StaticJavaParser.parse(
                "public class Foo { //comment\n" +
                "  private String a;\n" +
                "}\n"
                );
        LexicalPreservingPrinter.setup(cu);
        // create a new field declaration
        VariableDeclarator variable = new VariableDeclarator(new ClassOrInterfaceType("String"), "b");
        FieldDeclaration fd = new FieldDeclaration(new NodeList(Modifier.privateModifier()), variable);
        Optional<ClassOrInterfaceDeclaration> cid = cu.findFirst(ClassOrInterfaceDeclaration.class);
        // add the new variable
        cid.get().getMembers().addFirst(fd);
        assertTrue(LexicalPreservingPrinter.print(cu).equals(expected));
    }
}
