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
