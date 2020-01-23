/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package org.javaparser.symbolsolver.resolution.types;

import org.javaparser.resolution.types.ResolvedPrimitiveType;
import org.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class ResolvedPrimitiveTypeTest extends AbstractResolutionTest {

    @Test
    void byNameValidOptions() {
        assertEquals(ResolvedPrimitiveType.BOOLEAN, ResolvedPrimitiveType.byName("boolean"));
        assertEquals(ResolvedPrimitiveType.CHAR, ResolvedPrimitiveType.byName("char"));
        assertEquals(ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.byName("byte"));
        assertEquals(ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.byName("short"));
        assertEquals(ResolvedPrimitiveType.INT, ResolvedPrimitiveType.byName("int"));
        assertEquals(ResolvedPrimitiveType.LONG, ResolvedPrimitiveType.byName("long"));
        assertEquals(ResolvedPrimitiveType.FLOAT, ResolvedPrimitiveType.byName("float"));
        assertEquals(ResolvedPrimitiveType.DOUBLE, ResolvedPrimitiveType.byName("double"));
    }

    @Test
    void byNameInValidOptions() {
        assertThrows(IllegalArgumentException.class, () -> ResolvedPrimitiveType.byName("unexisting"));
    }
}
