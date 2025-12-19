/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

package com.github.javaparser.ast.expr;

import static com.github.javaparser.StaticJavaParser.parseSimpleName;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verifyNoInteractions;

import com.github.javaparser.ast.observer.AstObserver;
import org.junit.jupiter.api.Test;

class SimpleNameTest {

    @Test
    void defaultConstructorSetsIdentifierToEmpty() {
        assertEquals("empty", new SimpleName().getIdentifier());
    }

    @Test
    void identifierMustNotBeEmpty() {
        assertThrows(AssertionError.class, () -> new SimpleName(""));
    }

    @Test
    void identifierMustNotBeNull() {
        assertThrows(AssertionError.class, () -> new SimpleName(null));
    }

    @Test
    void unicodeEscapesArePreservedInIdentifiers() {
        SimpleName name = parseSimpleName("xxx\\u2122xxx");
        assertEquals("xxx\\u2122xxx", name.asString());
    }

    @Test
    void issue4791Test() {
        String a = new String("someName");
        String b = new String("someName");
        SimpleName expression = new SimpleName(a);

        AstObserver observer = mock(AstObserver.class);
        expression.register(observer);

        expression.setIdentifier(b);

        verifyNoInteractions(observer);
    }
}
