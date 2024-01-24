/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

package com.github.javaparser.ast.body;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Modifier.Keyword;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;
import static org.junit.jupiter.api.Assertions.*;

class FieldDeclarationTest {
    @Test
    void wofjweoifj() {
        CompilationUnit compilationUnit = parse("" +
                "class A {\n" +
                "    int a, b;\n" +
                "}");

        BodyDeclaration<?> declaration = compilationUnit.getType(0).getMembers().get(0);
        FieldDeclaration fieldDeclaration = declaration.asFieldDeclaration();
        VariableDeclarator var1 = fieldDeclaration.getVariables().get(0);
        VariableDeclarator var2 = fieldDeclaration.getVariables().get(1);
        assertEquals(var1, var1.getType().getParentNode().get());
        assertEquals(var2, var2.getType().getParentNode().get());
    }
    
    @Test
    void setModifiersPrimitiveType() {
    	FieldDeclaration field = parseBodyDeclaration("public static final int var = 1;").asFieldDeclaration();
    	testChangingModifiers(field);
    }
    
    @Test
    void setModifiersNonPrimitiveType() {
    	FieldDeclaration field = parseBodyDeclaration("public static final String var = \"a\";").asFieldDeclaration();
    	testChangingModifiers(field);
    }
    
    private void testChangingModifiers(FieldDeclaration field) {
    	NodeList<Modifier> modifiers = field.getModifiers();
    	assertTrue(modifiers.contains(Modifier.publicModifier()));
    	assertTrue(modifiers.contains(Modifier.staticModifier()));
    	assertTrue(modifiers.contains(Modifier.finalModifier()));
    	assertEquals(3, modifiers.size());
    	
    	field.setModifiers(new NodeList<Modifier>());
    	modifiers = field.getModifiers();
    	assertEquals(0, modifiers.size());
    	
    	field.setModifiers(Keyword.PRIVATE, Keyword.SYNCHRONIZED);
    	modifiers = field.getModifiers();
    	assertTrue(modifiers.contains(Modifier.privateModifier()));
    	assertTrue(modifiers.contains(Modifier.synchronizedModifier()));
    	assertEquals(2, modifiers.size());
    }

    @Test
    void interfaceFieldTest() {
        CompilationUnit compilationUnit = parse("" +
                "interface A {\n" +
                "    int a = 1;\n" +
                "    static int a_s = 1;\n" +
                "    final int a_f = 1;\n" +
                "    static final int a_s_f = 1;\n" +
                "    String b = \"b\";\n" +
                "    static String b_s = \"b\";\n" +
                "    final String b_f = \"b\";\n" +
                "    static final String b_s_f = \"b\";\n" +
                "}\n");
        for (int i = 0; i < 8; ++i) {
            BodyDeclaration<?> declaration = compilationUnit.getType(0).getMembers().get(i);
            FieldDeclaration fieldDeclaration = declaration.asFieldDeclaration();
            Assertions.assertTrue(fieldDeclaration.isStatic());
            Assertions.assertTrue(fieldDeclaration.isFinal());
        }
    }

    /**
     * Regression test for issue #4056.
     */
    @Test
    void testEnumWithPrivateFieldInsideInterface() {
        String source = "interface Outer {\n" +
                        "  enum Numbers {\n" +
                        "    ONE(1),\n" +
                        "    TWO(2),\n" +
                        "    THREE(3);\n" +
                        "\n" +
                        "    Numbers(int i) {\n" +
                        "      this.i = i;\n" +
                        "    }\n" +
                        "\n" +
                        "    private int i;\n" +
                        "  }\n" +
                        "}";
        CompilationUnit cu = StaticJavaParser.parse(source);
        FieldDeclaration i = cu.getTypes().get(0).asClassOrInterfaceDeclaration()
                .getMembers().get(0).asEnumDeclaration()
                .getFields().get(0);
        assertAll(
                () -> assertFalse(i.isPublic()),
                () -> assertFalse(i.isStatic()),
                () -> assertFalse(i.isFinal())
        );
    }

    @Test
    public void testFieldWithModifiers() {
        NodeList<Modifier> modifiers = new NodeList<>();
        modifiers.add(Modifier.publicModifier());
        modifiers.add(Modifier.staticModifier());

        Type type = new ClassOrInterfaceType("String");
        String name = "fieldName";

        FieldDeclaration field = new FieldDeclaration(modifiers, type, name);
        assertTrue(field.getModifiers().contains(Modifier.publicModifier()));
        assertTrue(field.getModifiers().contains(Modifier.staticModifier()));
    }

    @Test
    public void testGetModifiers() {
        FieldDeclaration field = new FieldDeclaration();
        NodeList<Modifier> modifiers = new NodeList<>();
        modifiers.add(Modifier.publicModifier());
        field.setModifiers(modifiers);
        assertTrue(field.getModifiers().contains(Modifier.publicModifier()));
    }

    @Test
    public void testSetVariables() {
        FieldDeclaration field = new FieldDeclaration();
        NodeList<VariableDeclarator> variables = new NodeList<>();
        VariableDeclarator var = new VariableDeclarator(new ClassOrInterfaceType("String"), "testVar");
        variables.add(var);
        field.setVariables(variables);
        assertEquals("testVar", field.getVariables().get(0).getNameAsString());
    }

    @Test
    public void testCreateGetter() {
        ClassOrInterfaceDeclaration mockClass = new ClassOrInterfaceDeclaration();
        FieldDeclaration field = mockClass.addField(int.class, "sampleField", Modifier.Keyword.PRIVATE);

        MethodDeclaration generatedGetter = field.createGetter();

        assertEquals("getSampleField", generatedGetter.getNameAsString());
        assertEquals(PrimitiveType.intType(), generatedGetter.getType());
        assertNotNull(generatedGetter.getBody().get());
    }

    @Test
    public void testCreateSetter() {
        ClassOrInterfaceDeclaration mockClass = new ClassOrInterfaceDeclaration();
        FieldDeclaration field = mockClass.addField(int.class, "sampleField", Modifier.Keyword.PRIVATE);

        MethodDeclaration generatedSetter = field.createSetter();

        assertEquals("setSampleField", generatedSetter.getNameAsString());
        assertEquals(1, generatedSetter.getParameters().size());
        assertEquals("sampleField", generatedSetter.getParameter(0).getNameAsString());
    }

    @Test
    public void testIsTransient() {
        FieldDeclaration field = new FieldDeclaration();
        assertFalse(field.isTransient());

        NodeList<Modifier> modifiers = new NodeList<>();
        modifiers.add(Modifier.transientModifier());
        field.setModifiers(modifiers);
        assertTrue(field.isTransient());
    }

    @Test
    public void testSetTransient() {
        FieldDeclaration field = new FieldDeclaration();
        assertFalse(field.isTransient());
        field.setTransient(true);
        assertTrue(field.isTransient());
    }

    @Test
    public void testIsVolatile() {
        FieldDeclaration field = new FieldDeclaration();
        assertFalse(field.isVolatile());

        NodeList<Modifier> modifiers = new NodeList<>();
        modifiers.add(Modifier.volatileModifier());
        field.setModifiers(modifiers);
        assertTrue(field.isVolatile());
    }

    @Test
    public void testSetVolatile() {
        FieldDeclaration field = new FieldDeclaration();
        assertFalse(field.isVolatile());
        field.setVolatile(true);
        assertTrue(field.isVolatile());
    }

    @Test
    public void testIsStatic() {
        FieldDeclaration field = new FieldDeclaration();
        assertFalse(field.isStatic());

        NodeList<Modifier> modifiers = new NodeList<>();
        modifiers.add(Modifier.staticModifier());
        field.setModifiers(modifiers);
        assertTrue(field.isStatic());
    }

    @Test
    public void testIsFinal() {
        FieldDeclaration field = new FieldDeclaration();
        assertFalse(field.isFinal());

        NodeList<Modifier> modifiers = new NodeList<>();
        modifiers.add(Modifier.finalModifier());
        field.setModifiers(modifiers);
        assertTrue(field.isFinal());
    }

    @Test
    public void testIsPublic() {
        FieldDeclaration field = new FieldDeclaration();
        assertFalse(field.isPublic());

        NodeList<Modifier> modifiers = new NodeList<>();
        modifiers.add(Modifier.publicModifier());
        field.setModifiers(modifiers);
        assertTrue(field.isPublic());
    }

    @Test
    public void testRemoveVariableNode() {
        FieldDeclaration field = new FieldDeclaration();
        VariableDeclarator variable = new VariableDeclarator(PrimitiveType.intType(), "testVar");
        field.addVariable(variable);

        assertTrue(field.getVariables().contains(variable));
        assertTrue(field.remove(variable));
        assertFalse(field.getVariables().contains(variable));
    }

    @Test
    public void testReplaceVariableNode() {
        FieldDeclaration field = new FieldDeclaration();
        VariableDeclarator originalVariable = new VariableDeclarator(PrimitiveType.intType(), "originalVar");
        field.addVariable(originalVariable);
        VariableDeclarator replacementVariable = new VariableDeclarator(PrimitiveType.intType(), "replacementVar");

        assertTrue(field.replace(originalVariable, replacementVariable));
        assertFalse(field.getVariables().contains(originalVariable));
        assertTrue(field.getVariables().contains(replacementVariable));
    }

    @Test
    public void testTypeCastingMethods() {
        FieldDeclaration field = new FieldDeclaration();

        assertTrue(field.isFieldDeclaration());
        assertEquals(field, field.asFieldDeclaration());
        field.ifFieldDeclaration(e -> {
            assertTrue(e instanceof FieldDeclaration);
        });

        assertTrue(field.toFieldDeclaration().isPresent());
    }
}
