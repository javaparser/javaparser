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

package com.github.javaparser;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class PositionTest {

    @Test
    public void testOrIfInvalid() {
        Position p1 = new Position(1, 1);
        Position p2 = new Position(2, 2);

        assertEquals(p1, p1.orIfInvalid(p2));

        Position invalid = new Position(0, 0);
        Position invalid2 = new Position(0, 1);

        assertEquals(p1, invalid.orIfInvalid(p1));
        assertEquals(invalid2, invalid2.orIfInvalid(invalid));
    }

    @Test
    public void testPositionExceptionFormat() {
        IllegalArgumentException thrown1 = Assertions.assertThrows(IllegalArgumentException.class,
                () -> new Position(-10, 1));

        assertEquals("Can't position at line -10", thrown1.getMessage());

        IllegalArgumentException thrown2 = Assertions.assertThrows(IllegalArgumentException.class,
                () -> new Position(1, -10));

        assertEquals("Can't position at column -10", thrown2.getMessage());
    }

}
