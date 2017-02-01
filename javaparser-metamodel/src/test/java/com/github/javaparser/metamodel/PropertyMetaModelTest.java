package com.github.javaparser.metamodel;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.BodyDeclaration;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;

public class PropertyMetaModelTest {
    @Test
    public void whenPropertyIsVerySimpleThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", int.class, Optional.empty(), false, false, false, false, false);
        assertEquals("int", bert.getTypeName());
        assertEquals("int", bert.getTypeNameGenerified());
        assertEquals("int", bert.getTypeNameForGetter());
        assertEquals("int", bert.getTypeNameForSetter());
    }

    @Test
    public void whenPropertyIsVeryComplexThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", BodyDeclaration.class, Optional.empty(), true, false, true, false, true);
        assertEquals("BodyDeclaration", bert.getTypeName());
        assertEquals("BodyDeclaration<?>", bert.getTypeNameGenerified());
        assertEquals("Optional<NodeList<BodyDeclaration<?>>>", bert.getTypeNameForGetter());
        assertEquals("NodeList<BodyDeclaration<?>>", bert.getTypeNameForSetter());
    }

    @Test
    public void whenPropertyIsAnEnumThenTypeInfoIsCorrect() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", Modifier.class, Optional.empty(), false, false, false, true, false);
        assertEquals("Modifier", bert.getTypeName());
        assertEquals("Modifier", bert.getTypeNameGenerified());
        assertEquals("EnumSet<Modifier>", bert.getTypeNameForGetter());
        assertEquals("EnumSet<Modifier>", bert.getTypeNameForSetter());
    }

    @Test
    public void metaModelFieldName() {
        PropertyMetaModel bert = new PropertyMetaModel(null, "bert", Modifier.class, Optional.empty(), false, false, false, true, false);
        assertEquals("bertPropertyMetaModel", bert.getMetaModelFieldName());
    }

}
