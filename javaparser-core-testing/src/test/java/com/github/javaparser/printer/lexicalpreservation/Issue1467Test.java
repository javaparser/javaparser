package com.github.javaparser.printer.lexicalpreservation;

/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ast.Modifier.Keyword;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Test;

public class Issue1467Test extends AbstractLexicalPreservingTest {
    
    @Test
    public void test() {
        considerCode(
                "public class Bar {\n" + 
                        "    public void foo() {\n" + 
                        "        System.out.print(\"Hello\");\n" + 
                        "    }\n" + 
                        "}");
        String expected = 
                "public void f() {\n" + 
                "        throw new UnsupportedOperationException(\"Not supported yet.\");\n" +
                "    }" ;
        // add method declaration
        MethodDeclaration decl = cu.getChildNodesByType(ClassOrInterfaceDeclaration.class).get(0).addMethod("f", Keyword.PUBLIC);
        // create body 
        BlockStmt body = new BlockStmt();
        NodeList<Statement> statements = new NodeList<>();
        ObjectCreationExpr exception = new ObjectCreationExpr();
        exception.setType("UnsupportedOperationException");
        NodeList<Expression> arguments = new NodeList<>();
        arguments.add(new StringLiteralExpr("Not supported yet."));
        exception.setArguments(arguments);
        statements.add(new ThrowStmt(exception));
        body.setStatements(statements);
        // set body to the method declaration
        decl.setBody(body);
        // print the result from LexicalPreservingPrinter
        String actual = LexicalPreservingPrinter.print(decl);
        TestUtils.assertEqualsStringIgnoringEol(expected, actual);
    }
}
