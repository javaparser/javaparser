package com.github.javaparser.metamodel;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.BodyDeclaration;
import org.junit.Test;

import static org.junit.Assert.*;

public class PropertyMetaModelTest {
    @Test
    public void whenPropertyIsVerySimpleThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", int.class, null, false, false, false, false, false);
        assertEquals("int", bert.getRawTypeName());
        assertEquals("int", bert.getTypeName());
        assertEquals("int", bert.getFullTypeNameForGetter());
        assertEquals("int", bert.getFullTypeNameForSetter());
    }

    @Test
    public void whenPropertyIsVeryComplexThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", BodyDeclaration.class, null, true, true, true, false, true);
        assertEquals("BodyDeclaration", bert.getRawTypeName());
        assertEquals("BodyDeclaration<?>", bert.getTypeName());
        assertEquals("Optional<NodeList<BodyDeclaration<?>>>", bert.getFullTypeNameForGetter());
        assertEquals("NodeList<BodyDeclaration<?>>", bert.getFullTypeNameForSetter());
    }

    @Test
    public void whenPropertyIsAnEnumThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", Modifier.class, null, false, false, false, true, false);
        assertEquals("Modifier", bert.getRawTypeName());
        assertEquals("Modifier", bert.getTypeName());
        assertEquals("EnumSet<Modifier>", bert.getFullTypeNameForGetter());
        assertEquals("EnumSet<Modifier>", bert.getFullTypeNameForSetter());
    }

}