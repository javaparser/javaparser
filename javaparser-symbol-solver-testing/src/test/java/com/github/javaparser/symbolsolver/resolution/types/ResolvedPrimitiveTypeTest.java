/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution.types;

import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
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
