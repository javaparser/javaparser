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

import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.JavaParser.parseVariableDeclarationExpr;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public class NodeWithVariablesTest {

    @Test
    public void getCommonTypeWorksForNormalVariables() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a,b");
        assertEquals(PrimitiveType.intType(), declaration.getCommonType());
    }

    @Test
    public void getCommonTypeWorksForArrayTypes() {
        parseVariableDeclarationExpr("int a[],b[]").getCommonType();
    }

    @Test
    public void getCommonTypeFailsOnArrayDifferences() {
        assertThrows(AssertionError.class, () ->
                parseVariableDeclarationExpr("int a[],b[][]").getCommonType());
    }

    @Test
    public void getCommonTypeFailsOnDodgySetterUsage() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a,b");
        assertThrows(AssertionError.class, () -> declaration.getVariable(1).setType(String.class));
    }

    @Test
    public void getCommonTypeFailsOnInvalidEmptyVariableList() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a");
        declaration.getVariables().clear();
        assertThrows(AssertionError.class, declaration::getCommonType);
    }

    @Test
    public void getElementTypeWorksForNormalVariables() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a,b");
        assertEquals(PrimitiveType.intType(), declaration.getElementType());
    }

    @Test
    public void getElementTypeWorksForArrayTypes() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a[],b[]");
        assertEquals(PrimitiveType.intType(), declaration.getElementType());
    }

    @Test
    public void getElementTypeIsOkayWithArrayDifferences() {
        parseVariableDeclarationExpr("int a[],b[][]").getElementType();
    }

    @Test
    public void getElementTypeFailsOnDodgySetterUsage() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a,b");
        assertThrows(AssertionError.class, ()->declaration.getVariable(1).setType(String.class));
    }

    @Test
    public void getElementTypeFailsOnInvalidEmptyVariableList() {
        VariableDeclarationExpr declaration = parseVariableDeclarationExpr("int a");
        declaration.getVariables().clear();
        assertThrows(AssertionError.class, declaration::getElementType);
    }

}