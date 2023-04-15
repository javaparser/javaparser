/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.SimpleName;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

public class WalkFindTest {
    @Test
    void findCompilationUnit() {
        CompilationUnit cu = parse("class X{int x;}");
        VariableDeclarator x = cu.getClassByName("X").get().getMember(0).asFieldDeclaration().getVariables().get(0);
        assertEquals(cu, x.findCompilationUnit().get());
    }

    @Test
    void findParent() {
        CompilationUnit cu = parse("class X{int x;}");
        SimpleName x = cu.getClassByName("X").get().getMember(0).asFieldDeclaration().getVariables().get(0).getName();
        assertEquals("int x;", x.findAncestor(FieldDeclaration.class).get().toString());
    }
    
    @Test
    void findParentFromTypes() {
        CompilationUnit cu = parse("class X{Integer x;}");
        VariableDeclarator vd = cu.getClassByName("X").get().getMember(0).asFieldDeclaration().getVariables().get(0);
        assertEquals(FieldDeclaration.class.getName(),
                vd.findAncestor(new Class[] { CompilationUnit.class, ClassOrInterfaceDeclaration.class, FieldDeclaration.class }).get().getClass()
                        .getName());
        assertEquals(ClassOrInterfaceDeclaration.class.getName(),
                vd.findAncestor(new Class[] { CompilationUnit.class, ClassOrInterfaceDeclaration.class }).get().getClass()
                        .getName());
    }

    @Test
    void cantFindCompilationUnit() {
        VariableDeclarator x = new VariableDeclarator();
        assertFalse(x.findCompilationUnit().isPresent());
    }

    @Test
    void genericWalk() {
        Expression e = parseExpression("1+1");
        StringBuilder b = new StringBuilder();
        e.walk(n -> b.append(n.toString()));
        assertEquals("1 + 111", b.toString());
    }

    @Test
    void classSpecificWalk() {
        Expression e = parseExpression("1+1");
        StringBuilder b = new StringBuilder();
        e.walk(IntegerLiteralExpr.class, n -> b.append(n.toString()));
        assertEquals("11", b.toString());
    }

    @Test
    void conditionalFindAll() {
        Expression e = parseExpression("1+2+3");
        List<IntegerLiteralExpr> ints = e.findAll(IntegerLiteralExpr.class, n -> n.asInt() > 1);
        assertEquals("[2, 3]", ints.toString());
    }

    @Test
    void typeOnlyFindAll() {
        Expression e = parseExpression("1+2+3");
        List<IntegerLiteralExpr> ints = e.findAll(IntegerLiteralExpr.class);
        assertEquals("[1, 2, 3]", ints.toString());
    }

    @Test
    void typeOnlyFindAllMatchesSubclasses() {
        Expression e = parseExpression("1+2+3");
        List<Node> ints = e.findAll(Node.class);
        assertEquals("[1 + 2 + 3, 1 + 2, 1, 2, 3]", ints.toString());
    }

    @Test
    void conditionalTypedFindFirst() {
        Expression e = parseExpression("1+2+3");
        Optional<IntegerLiteralExpr> ints = e.findFirst(IntegerLiteralExpr.class, n -> n.asInt() > 1);
        assertEquals("Optional[2]", ints.toString());
    }

    @Test
    void typeOnlyFindFirst() {
        Expression e = parseExpression("1+2+3");
        Optional<IntegerLiteralExpr> ints = e.findFirst(IntegerLiteralExpr.class);
        assertEquals("Optional[1]", ints.toString());
    }

    @Test
    void stream() {
        Expression e = parseExpression("1+2+3");
        List<IntegerLiteralExpr> ints = e.stream()
                .filter(n -> n instanceof IntegerLiteralExpr)
                .map(IntegerLiteralExpr.class::cast)
                .filter(i -> i.asInt() > 1)
                .collect(Collectors.toList());
        assertEquals("[2, 3]", ints.toString());
    }

}
