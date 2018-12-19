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

package com.github.javaparser.builders;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.Test;

import java.util.List;

import static com.github.javaparser.JavaParser.parseClassOrInterfaceType;
import static com.github.javaparser.JavaParser.parseExpression;
import static com.github.javaparser.JavaParser.parseType;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class NodeWithMembersBuildersTest {
    private final CompilationUnit cu = new CompilationUnit();
    private final ClassOrInterfaceDeclaration classDeclaration = cu.addClass("test");

    @Test
    public void testAddField() {
        FieldDeclaration addField = classDeclaration.addField(int.class, "fieldName", Modifier.PRIVATE);
        assertEquals(1, classDeclaration.getMembers().size());
        assertEquals(addField, classDeclaration.getMember(0));
        assertEquals("fieldName", addField.getVariable(0).getNameAsString());
    }

    @Test
    public void testAddMethod() {
        MethodDeclaration addMethod = classDeclaration.addMethod("foo", Modifier.PUBLIC);
        assertEquals(1, classDeclaration.getMembers().size());
        assertEquals(addMethod, classDeclaration.getMember(0));
        assertEquals("foo", addMethod.getNameAsString());
    }

    @Test
    public void testAddCtor() {
        ConstructorDeclaration addCtor = classDeclaration.addConstructor(Modifier.PUBLIC);
        assertEquals(1, classDeclaration.getMembers().size());
        assertEquals(addCtor, classDeclaration.getMember(0));
        assertEquals(classDeclaration.getName(), addCtor.getName());
    }

    @Test
    public void testAddInitializers() {
        classDeclaration.addInitializer();
        assertEquals(1, classDeclaration.getMembers().size());
        assertEquals(InitializerDeclaration.class, classDeclaration.getMember(0).getClass());

        classDeclaration.addStaticInitializer();
        assertEquals(2, classDeclaration.getMembers().size());
        assertEquals(InitializerDeclaration.class, classDeclaration.getMember(0).getClass());
    }

    @Test
    public void testGetMethodsWithName() {
        MethodDeclaration addMethod = classDeclaration.addMethod("foo", Modifier.PUBLIC);
        MethodDeclaration addMethod2 = classDeclaration.addMethod("foo", Modifier.PUBLIC).addParameter(int.class, "overload");
        List<MethodDeclaration> methodsByName = classDeclaration.getMethodsByName("foo");
        assertEquals(2, methodsByName.size());
        assertTrue(methodsByName.contains(addMethod));
        assertTrue(methodsByName.contains(addMethod2));
    }

    @Test
    public void testGetMethods() {
        MethodDeclaration addMethod = classDeclaration.addMethod("foo", Modifier.PUBLIC);
        MethodDeclaration addMethod2 = classDeclaration.addMethod("foo", Modifier.PUBLIC).addParameter(int.class, "overload");

        List<MethodDeclaration> methods = classDeclaration.getMethods();

        assertEquals(2, methods.size());
        assertTrue(methods.contains(addMethod));
        assertTrue(methods.contains(addMethod2));
    }

    @Test
    public void testGetMethodsWithParameterTypes() {
        classDeclaration.addMethod("foo", Modifier.PUBLIC);
        MethodDeclaration addMethod2 = classDeclaration.addMethod("foo", Modifier.PUBLIC).addParameter(int.class, "overload");
        ClassOrInterfaceType type = parseClassOrInterfaceType("List");
        type.setTypeArguments(parseClassOrInterfaceType("String"));
        MethodDeclaration methodWithListParam = classDeclaration.addMethod("fooList", Modifier.PUBLIC).addParameter(type, "overload");
        MethodDeclaration addMethod3 = classDeclaration.addMethod("foo2", Modifier.PUBLIC).addParameter(int.class, "overload");

        List<MethodDeclaration> methodsByParam = classDeclaration.getMethodsByParameterTypes(int.class);
        assertEquals(2, methodsByParam.size());
        assertTrue(methodsByParam.contains(addMethod2));
        assertTrue(methodsByParam.contains(addMethod3));
        List<MethodDeclaration> methodsByParam2 = classDeclaration.getMethodsByParameterTypes("List<String>");
        assertEquals(1, methodsByParam2.size());
        assertTrue(methodsByParam2.contains(methodWithListParam));
    }

    @Test
    public void testGetFieldWithName() {
        FieldDeclaration addField = classDeclaration.addField(int.class, "fieldName", Modifier.PRIVATE);
        classDeclaration.addField(float.class, "secondField", Modifier.PRIVATE);
        FieldDeclaration fieldByName = classDeclaration.getFieldByName("fieldName").get();
        assertEquals(addField, fieldByName);
    }

    @Test
    public void testGetFields() {
        FieldDeclaration firstField = classDeclaration.addField(int.class, "fieldName", Modifier.PRIVATE);
        FieldDeclaration secondField = classDeclaration.addField(float.class, "secondField", Modifier.PRIVATE);

        List<FieldDeclaration> fields = classDeclaration.getFields();

        assertTrue(fields.contains(firstField));
        assertTrue(fields.contains(secondField));
    }

    @Test
    public void testAddPrivateFieldWithType(){
        CompilationUnit compilationUnit = new CompilationUnit();
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = compilationUnit.addClass("Person");
        classOrInterfaceDeclaration.addPrivateField(parseType("java.lang.String"), "name");

        assertNotNull(classOrInterfaceDeclaration.getFields());
        assertEquals(1, classOrInterfaceDeclaration.getFields().size());

        FieldDeclaration fieldDeclaration = classOrInterfaceDeclaration.getFields().get(0);
        assertEquals(Modifier.PRIVATE, fieldDeclaration.getModifiers().iterator().next());
        assertEquals("java.lang.String",fieldDeclaration.getVariables().get(0).getType().toString());
        assertEquals("name",fieldDeclaration.getVariables().get(0).getName().toString());
    }

    @Test
    public void testAddPublicFieldWithType(){
        CompilationUnit compilationUnit = new CompilationUnit();
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = compilationUnit.addClass("Person");
        classOrInterfaceDeclaration.addPublicField(parseType("java.lang.String"), "name");

        assertNotNull(classOrInterfaceDeclaration.getFields());
        assertEquals(1, classOrInterfaceDeclaration.getFields().size());

        FieldDeclaration fieldDeclaration = classOrInterfaceDeclaration.getFields().get(0);
        assertEquals(Modifier.PUBLIC, fieldDeclaration.getModifiers().iterator().next());
        assertEquals("java.lang.String",fieldDeclaration.getVariables().get(0).getType().toString());
        assertEquals("name",fieldDeclaration.getVariables().get(0).getName().toString());
    }

    @Test
    public void testAddProtectedFieldWithType(){
        CompilationUnit compilationUnit = new CompilationUnit();
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = compilationUnit.addClass("Person");
        classOrInterfaceDeclaration.addProtectedField(parseType("java.lang.String"), "name");

        assertNotNull(classOrInterfaceDeclaration.getFields());
        assertEquals(1, classOrInterfaceDeclaration.getFields().size());

        FieldDeclaration fieldDeclaration = classOrInterfaceDeclaration.getFields().get(0);
        assertEquals(Modifier.PROTECTED, fieldDeclaration.getModifiers().iterator().next());
        assertEquals("java.lang.String",fieldDeclaration.getVariables().get(0).getType().toString());
        assertEquals("name",fieldDeclaration.getVariables().get(0).getName().toString());
    }

    @Test
    public void testClassWithInitializersWithString(){
        CompilationUnit compilationUnit = new CompilationUnit();
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = compilationUnit.addClass("Person");
        classOrInterfaceDeclaration.addFieldWithInitializer(
                "java.lang.String",
                "name",
                parseExpression("John"),
                Modifier.PUBLIC);
        assertNotNull(classOrInterfaceDeclaration.getFields());
        assertEquals(1, classOrInterfaceDeclaration.getFields().size());

        FieldDeclaration fieldDeclaration = classOrInterfaceDeclaration.getFields().get(0);
        assertEquals(Modifier.PUBLIC, fieldDeclaration.getModifiers().iterator().next());
        assertEquals("java.lang.String",fieldDeclaration.getVariables().get(0).getType().toString());
        assertEquals("name",fieldDeclaration.getVariables().get(0).getName().toString());
        assertEquals("John",fieldDeclaration.getVariables().get(0).getInitializer().get().toString());
    }

    @Test
    public void testClassWithInitializersWithClass(){
        CompilationUnit compilationUnit = new CompilationUnit();
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = compilationUnit.addClass("Person");
        classOrInterfaceDeclaration.addFieldWithInitializer(
                List.class,
                "skills",
                parseExpression("new ArrayList()"),
                Modifier.PUBLIC);
        assertNotNull(classOrInterfaceDeclaration.getFields());
        assertEquals(1, classOrInterfaceDeclaration.getFields().size());

        FieldDeclaration fieldDeclaration = classOrInterfaceDeclaration.getFields().get(0);
        assertEquals(Modifier.PUBLIC, fieldDeclaration.getModifiers().iterator().next());
        assertEquals("List",fieldDeclaration.getVariables().get(0).getType().toString());
        assertEquals("skills",fieldDeclaration.getVariables().get(0).getName().toString());
        assertEquals("new ArrayList()",fieldDeclaration.getVariables().get(0).getInitializer().get().toString());
    }
}
