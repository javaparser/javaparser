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

package com.github.javaparser.remove;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class NodeRemovalTest {
    private final CompilationUnit cu = new CompilationUnit();

    @Test
    public void testRemoveClassFromCompilationUnit() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("test");
        assertEquals(1, cu.getTypes().size());
        boolean remove = testClass.remove();
        assertEquals(true, remove);
        assertEquals(0, cu.getTypes().size());
    }

    @Test
    public void testRemoveFieldFromClass() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("test");

        FieldDeclaration addField = testClass.addField(String.class, "test");
        assertEquals(1, testClass.getMembers().size());
        boolean remove = addField.remove();
        assertEquals(true, remove);
        assertEquals(0, testClass.getMembers().size());
    }

    @Test
    public void testRemoveStatementFromMethodBody() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("testC");

        MethodDeclaration addMethod = testClass.addMethod("testM");
        BlockStmt methodBody = addMethod.createBody();
        Statement addStatement = methodBody.addAndGetStatement("test");
        assertEquals(1, methodBody.getStatements().size());
        boolean remove = addStatement.remove();
        assertEquals(true, remove);
        assertEquals(0, methodBody.getStatements().size());
    }
}
