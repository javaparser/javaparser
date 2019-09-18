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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseVariableDeclarationExpr;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class NodeWithVariablesTest {

    @Test
    void getCommonTypeWorksForNormalVariables() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a,b");
        assertEquals(PrimitiveType.intType(), declaration.getCommonType());
    }

    @Test
    void getCommonTypeWorksForArrayTypes() {
        parseVariableDeclarationExpr("int a[],b[]").getCommonType();
    }

    @Test
    void getCommonTypeFailsOnArrayDifferences() {
        assertThrows(AssertionError.class, () -> parseVariableDeclarationExpr("int a[],b[][]").getCommonType());
    }

    @Test
    void getCommonTypeFailsOnDodgySetterUsage() {
        assertThrows(AssertionError.class, () -> {
            VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a,b");
            declaration.getVariable(1).setType(String.class);
            declaration.getCommonType();
        });
    }

    @Test
    void getCommonTypeFailsOnInvalidEmptyVariableList() {
        assertThrows(AssertionError.class, () -> {
            VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a");
            declaration.getVariables().clear();
            declaration.getCommonType();
        });
    }

    @Test
    void getElementTypeWorksForNormalVariables() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a,b");
        assertEquals(PrimitiveType.intType(), declaration.getElementType());
    }

    @Test
    void getElementTypeWorksForArrayTypes() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a[],b[]");
        assertEquals(PrimitiveType.intType(), declaration.getElementType());
    }

    @Test
    void getElementTypeIsOkayWithArrayDifferences() {
        parseVariableDeclarationExpr("int a[],b[][]").getElementType();
    }

    @Test
    void getElementTypeFailsOnDodgySetterUsage() {
        assertThrows(AssertionError.class, () -> {
            VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a,b");
            declaration.getVariable(1).setType(String.class);
            declaration.getElementType();
        });
    }

    @Test
    void getElementTypeFailsOnInvalidEmptyVariableList() {
        assertThrows(AssertionError.class, () -> {
            VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a");
            declaration.getVariables().clear();
            declaration.getElementType();
        });
    }

    @Test
    void setAllTypesWorks() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int[] a[],b[][]");
        declaration.setAllTypes(StaticJavaParser.parseType("Dog"));
        assertEquals("Dog a, b", declaration.toString());
    }
}