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

package com.github.javaparser.wiki_samples.removenode;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.visitor.ModifierVisitor;

import java.io.FileInputStream;

public class ModifierVisitorTest {

    public static void main(String... args) throws Exception {
        // parse the file
        CompilationUnit cu = JavaParser.parse(new FileInputStream("forGitHubTest.java"));

        // The visitor should remove all a=20 variable declarations.
        cu.accept(new MyVisitor(), null);

        System.out.println(cu.toString());
    }
}

class MyVisitor extends ModifierVisitor<Void> {
    @Override
    public Node visit(VariableDeclarator declarator, Void args) {
        if (declarator.getNameAsString().equals("a")
                // the initializer is optional, first check if there is one
                && declarator.getInitializer().isPresent()) {
            Expression expression = declarator.getInitializer().get();
            // We're looking for a literal integer.
            if (expression instanceof IntegerLiteralExpr) {
                // We found one. Is it literal integer 20?
                if (((IntegerLiteralExpr) expression).getValue().equals("20")) {
                    // Returning null means "remove this VariableDeclarator"
                    return null;
                }
            }
        }
        return declarator;
    }
}
