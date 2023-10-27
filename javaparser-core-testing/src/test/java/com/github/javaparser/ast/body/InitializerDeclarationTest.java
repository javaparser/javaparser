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

package com.github.javaparser.ast.body;

import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.metamodel.InitializerDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class InitializerDeclarationTest {

    @Test
    public void testDefaultConstructor() {
        InitializerDeclaration initializer = new InitializerDeclaration();
        assertNotNull(initializer.getBody());
        assertFalse(initializer.isStatic());
    }

    @Test
    public void testParameterizedConstructor() {
        BlockStmt blockStmt = new BlockStmt();
        InitializerDeclaration initializer = new InitializerDeclaration(true, blockStmt);
        assertEquals(blockStmt, initializer.getBody());
        assertTrue(initializer.isStatic());
    }

    @Test
    public void testSetStatic() {
        InitializerDeclaration initializer = new InitializerDeclaration();
        initializer.setStatic(true);
        assertTrue(initializer.isStatic());
    }

    @Test
    public void testSetBody() {
        InitializerDeclaration initializer = new InitializerDeclaration();
        BlockStmt blockStmt = new BlockStmt();
        initializer.setBody(blockStmt);
        assertEquals(blockStmt, initializer.getBody());
    }

    @Test
    public void testClone() {
        InitializerDeclaration initializer = new InitializerDeclaration(true, new BlockStmt());
        InitializerDeclaration cloned = initializer.clone();
        assertNotSame(initializer, cloned);
        assertEquals(initializer.isStatic(), cloned.isStatic());
    }

    @Test
    public void testGetMetaModel() {
        InitializerDeclaration initializer = new InitializerDeclaration();
        InitializerDeclarationMetaModel metaModel = initializer.getMetaModel();
        assertNotNull(metaModel);
        assertEquals(JavaParserMetaModel.initializerDeclarationMetaModel, metaModel);
    }

    @Test
    public void testReplaceBody() {
        InitializerDeclaration initializer = new InitializerDeclaration();
        BlockStmt oldBody = initializer.getBody();
        BlockStmt newBody = new BlockStmt();
        assertTrue(initializer.replace(oldBody, newBody));
        assertEquals(newBody, initializer.getBody());
    }

    @Test
    public void testReplaceWithNull() {
        InitializerDeclaration initializer = new InitializerDeclaration();
        assertFalse(initializer.replace(null, new BlockStmt()));
    }

    @Test
    public void testTypeCastingMethods() {
        InitializerDeclaration initializer = new InitializerDeclaration();

        assertTrue(initializer.isInitializerDeclaration());
        assertEquals(initializer, initializer.asInitializerDeclaration());
        initializer.ifInitializerDeclaration(e -> {
            assertTrue(e instanceof InitializerDeclaration);
        });

        assertTrue(initializer.toInitializerDeclaration().isPresent());
    }
}
