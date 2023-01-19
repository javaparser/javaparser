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

package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.CodeGenerationUtils.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class CodeGenerationUtilsTest {
    @Test
    void setters() {
        assertEquals("setValue", setterName("value"));
        assertEquals("setBlue", setterName("isBlue"));
    }

    @Test
    void getters() {
        assertEquals("getValue", getterName(Object.class, "value"));
        assertEquals("isBlue", getterName(boolean.class, "isBlue"));
        assertEquals("isBlue", getterName(boolean.class, "blue"));
        assertEquals("getBlue", getterName(Boolean.class, "blue"));
        assertEquals("getIsBlue", getterName(Boolean.class, "isBlue"));
    }

    @Test
    void testGetterToPropertyName() {
        assertEquals("value", getterToPropertyName("getValue"));
        assertEquals("blue", getterToPropertyName("isBlue"));
        assertEquals("value", getterToPropertyName("hasValue"));

        IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                () -> getterToPropertyName("value"));
        assertEquals("Unexpected getterName 'value'", thrown.getMessage());
    }

}
