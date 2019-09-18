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

package com.github.javaparser.ast;

import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;

import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class DataKeyTest {
    private static final DataKey<String> ABC = new DataKey<String>() {
    };
    private static final DataKey<String> DEF = new DataKey<String>() {
    };
    private static final DataKey<List<String>> LISTY = new DataKey<List<String>>() {
    };
    private static final DataKey<List<String>> DING = new DataKey<List<String>>() {
    };

    @Test
    void addAFewKeysAndSeeIfTheyAreStoredCorrectly() {
        Node node = new SimpleName();

        node.setData(ABC, "Hurray!");
        node.setData(LISTY, Arrays.asList("a", "b"));
        node.setData(ABC, "w00t");

        assertThat(node.getData(ABC)).contains("w00t");
        assertThat(node.getData(LISTY)).containsExactly("a", "b");
        assertThat(node.containsData(ABC)).isTrue();
        assertThat(node.containsData(LISTY)).isTrue();
        assertThat(node.containsData(DING)).isFalse();
    }

    @Test
    void aNonExistentKeyThrowsAnException() {
        Node node = new SimpleName();

        assertThrows(IllegalStateException.class, () -> node.getData(DING));
    }

    @Test
    void cloningCopiesData() {
        Node node = new SimpleName();
        node.setData(ABC, "ABC!");
        node.setData(DEF, "DEF!");

        Node clone = node.clone();
        assertEquals("ABC!", clone.getData(ABC));
        assertEquals("DEF!", clone.getData(DEF));
    }
}
