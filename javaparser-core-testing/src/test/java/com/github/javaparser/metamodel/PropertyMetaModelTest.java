/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.BodyDeclaration;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import org.junit.jupiter.api.Test;

class PropertyMetaModelTest {
    @Test
    void whenPropertyIsVerySimpleThenTypeInfoIsCorrect() {
        PropertyMetaModel bert =
                new PropertyMetaModel(null, "bert", int.class, Optional.empty(), false, false, false, false);
        assertEquals("int", bert.getTypeName());
        assertEquals("int", bert.getTypeNameGenerified());
        assertEquals("int", bert.getTypeNameForGetter());
        assertEquals("int", bert.getTypeNameForSetter());
    }

    @Test
    void whenPropertyIsVeryComplexThenTypeInfoIsCorrect() {
        PropertyMetaModel bert =
                new PropertyMetaModel(null, "bert", BodyDeclaration.class, Optional.empty(), true, false, true, true);
        assertEquals("BodyDeclaration", bert.getTypeName());
        assertEquals("BodyDeclaration<?>", bert.getTypeNameGenerified());
        assertEquals("Optional<NodeList<BodyDeclaration<?>>>", bert.getTypeNameForGetter());
        assertEquals("NodeList<BodyDeclaration<?>>", bert.getTypeNameForSetter());
    }

    @Test
    void whenPropertyIsANodeListThenTypeInfoIsCorrect() {
        PropertyMetaModel bert =
                new PropertyMetaModel(null, "bert", Modifier.class, Optional.empty(), false, false, true, false);
        assertEquals("Modifier", bert.getTypeName());
        assertEquals("Modifier", bert.getTypeNameGenerified());
        assertEquals("NodeList<Modifier>", bert.getTypeNameForGetter());
        assertEquals("NodeList<Modifier>", bert.getTypeNameForSetter());
    }

    @Test
    void metaModelFieldName() {
        PropertyMetaModel bert =
                new PropertyMetaModel(null, "bert", Modifier.class, Optional.empty(), false, false, false, false);
        assertEquals("bertPropertyMetaModel", bert.getMetaModelFieldName());
    }

    @Test
    void propertiesDeclaredByDifferentNodesAreNotEqual() {
        PropertyMetaModel nameIdentifier = JavaParserMetaModel.nameMetaModel.identifierPropertyMetaModel;
        PropertyMetaModel simpleNameIdentifier = JavaParserMetaModel.simpleNameMetaModel.identifierPropertyMetaModel;
        PropertyMetaModel methodReferenceIdentifier =
                JavaParserMetaModel.methodReferenceExprMetaModel.identifierPropertyMetaModel;
        Map<PropertyMetaModel, String> values = new HashMap<>();
        values.put(nameIdentifier, "Name value");
        values.put(simpleNameIdentifier, "SimpleName value");
        values.put(methodReferenceIdentifier, "MethodReferenceExpr value");

        assertAll(
                () -> assertNotEquals(nameIdentifier, simpleNameIdentifier),
                () -> assertNotEquals(nameIdentifier, methodReferenceIdentifier),
                () -> assertNotEquals(simpleNameIdentifier, methodReferenceIdentifier),
                () -> assertEquals(3, values.size()),
                () -> assertEquals("Name value", values.get(nameIdentifier)),
                () -> assertEquals("SimpleName value", values.get(simpleNameIdentifier)),
                () -> assertEquals("MethodReferenceExpr value", values.get(methodReferenceIdentifier)));
    }

    @Test
    void hashSetRetainsAllDeclaredProperties() {
        List<PropertyMetaModel> declaredProperties = new ArrayList<>();
        for (BaseNodeMetaModel nodeMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            declaredProperties.addAll(nodeMetaModel.getDeclaredPropertyMetaModels());
        }

        assertEquals(declaredProperties.size(), new HashSet<>(declaredProperties).size());
    }

    @Test
    void inheritedPropertiesRetainTheirDeclaringOwnerAndEquality() {
        PropertyMetaModel integerValue =
                JavaParserMetaModel.integerLiteralExprMetaModel.getAllPropertyMetaModels().stream()
                        .filter(p -> p.getName().equals("value"))
                        .findFirst()
                        .get();
        PropertyMetaModel doubleValue =
                JavaParserMetaModel.doubleLiteralExprMetaModel.getAllPropertyMetaModels().stream()
                        .filter(p -> p.getName().equals("value"))
                        .findFirst()
                        .get();

        assertSame(JavaParserMetaModel.literalStringValueExprMetaModel.valuePropertyMetaModel, integerValue);
        assertSame(integerValue, doubleValue);
        assertSame(JavaParserMetaModel.literalStringValueExprMetaModel, integerValue.getContainingNodeMetaModel());
    }

    @Test
    void propertiesWithNullOwnersRemainComparableAndHashable() {
        PropertyMetaModel first =
                new PropertyMetaModel(null, "identifier", String.class, Optional.empty(), false, false, false, false);
        PropertyMetaModel second =
                new PropertyMetaModel(null, "identifier", String.class, Optional.empty(), false, false, false, false);
        PropertyMetaModel withOwner = JavaParserMetaModel.simpleNameMetaModel.identifierPropertyMetaModel;

        assertAll(
                () -> assertEquals(first, second),
                () -> assertEquals(first.hashCode(), second.hashCode()),
                () -> assertNotEquals(first, withOwner),
                () -> assertNotEquals(withOwner, first));
    }
}
