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

package com.github.javaparser.resolution.types;

import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class ResolvedPrimitiveTypeTest extends AbstractResolutionTest {

    private String exampleOfSwitch(ResolvedPrimitiveType rpt) {
        switch (rpt) {
            case INT:
                return "I";
            case BYTE:
                return "B";
            case DOUBLE:
                return "D";
            default:
                return "U";
        }
    }

    @Test
    public void tryTheSwitchStatement() {
        assertEquals("U", exampleOfSwitch(ResolvedPrimitiveType.BOOLEAN));
        assertEquals("U", exampleOfSwitch(ResolvedPrimitiveType.CHAR));
        assertEquals("B", exampleOfSwitch(ResolvedPrimitiveType.BYTE));
        assertEquals("U", exampleOfSwitch(ResolvedPrimitiveType.SHORT));
        assertEquals("I", exampleOfSwitch(ResolvedPrimitiveType.INT));
        assertEquals("U", exampleOfSwitch(ResolvedPrimitiveType.LONG));
        assertEquals("U", exampleOfSwitch(ResolvedPrimitiveType.FLOAT));
        assertEquals("D", exampleOfSwitch(ResolvedPrimitiveType.DOUBLE));
    }
}
