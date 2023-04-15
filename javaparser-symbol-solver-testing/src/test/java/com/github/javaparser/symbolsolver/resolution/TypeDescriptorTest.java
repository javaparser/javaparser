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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.utils.TypeUtils;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class TypeDescriptorTest {
    @Test
    public void primitiveTypeDescriptorTest() {
        assertEquals("V", TypeUtils.getPrimitiveTypeDescriptor(void.class));
        assertEquals("V", TypeUtils.getPrimitiveTypeDescriptor(Void.class));

        assertEquals("Z", TypeUtils.getPrimitiveTypeDescriptor(boolean.class));
        assertEquals("Z", TypeUtils.getPrimitiveTypeDescriptor(Boolean.class));

        assertEquals("C", TypeUtils.getPrimitiveTypeDescriptor(char.class));
        assertEquals("C", TypeUtils.getPrimitiveTypeDescriptor(Character.class));

        assertEquals("B", TypeUtils.getPrimitiveTypeDescriptor(byte.class));
        assertEquals("B", TypeUtils.getPrimitiveTypeDescriptor(Byte.class));

        assertEquals("S", TypeUtils.getPrimitiveTypeDescriptor(short.class));
        assertEquals("S", TypeUtils.getPrimitiveTypeDescriptor(Short.class));

        assertEquals("I", TypeUtils.getPrimitiveTypeDescriptor(int.class));
        assertEquals("I", TypeUtils.getPrimitiveTypeDescriptor(Integer.class));

        assertEquals("J", TypeUtils.getPrimitiveTypeDescriptor(long.class));
        assertEquals("J", TypeUtils.getPrimitiveTypeDescriptor(Long.class));

        assertEquals("F", TypeUtils.getPrimitiveTypeDescriptor(float.class));
        assertEquals("F", TypeUtils.getPrimitiveTypeDescriptor(Float.class));

        assertEquals("D", TypeUtils.getPrimitiveTypeDescriptor(double.class));
        assertEquals("D", TypeUtils.getPrimitiveTypeDescriptor(Double.class));
    }
}
