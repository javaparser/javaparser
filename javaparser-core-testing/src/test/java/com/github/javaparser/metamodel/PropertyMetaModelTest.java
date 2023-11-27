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

package com.github.javaparser.metamodel;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.BodyDeclaration;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

class PropertyMetaModelTest {
    @Test
    void whenPropertyIsVerySimpleThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", int.class, Optional.empty(), false, false, false, false);
        assertEquals("int", bert.getTypeName());
        assertEquals("int", bert.getTypeNameGenerified());
        assertEquals("int", bert.getTypeNameForGetter());
        assertEquals("int", bert.getTypeNameForSetter());
    }

    @Test
    void whenPropertyIsVeryComplexThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", BodyDeclaration.class, Optional.empty(), true, false, true, true);
        assertEquals("BodyDeclaration", bert.getTypeName());
        assertEquals("BodyDeclaration<?>", bert.getTypeNameGenerified());
        assertEquals("Optional<NodeList<BodyDeclaration<?>>>", bert.getTypeNameForGetter());
        assertEquals("NodeList<BodyDeclaration<?>>", bert.getTypeNameForSetter());
    }

    @Test
    void whenPropertyIsANodeListThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", Modifier.class, Optional.empty(), false, false, true, false);
        assertEquals("Modifier", bert.getTypeName());
        assertEquals("Modifier", bert.getTypeNameGenerified());
        assertEquals("NodeList<Modifier>", bert.getTypeNameForGetter());
        assertEquals("NodeList<Modifier>", bert.getTypeNameForSetter());
    }

    @Test
    void metaModelFieldName() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", Modifier.class, Optional.empty(), false, false, false, false);
        assertEquals("bertPropertyMetaModel", bert.getMetaModelFieldName());
    }

}
