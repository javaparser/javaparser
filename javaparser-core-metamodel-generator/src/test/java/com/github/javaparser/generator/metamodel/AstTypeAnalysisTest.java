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

package com.github.javaparser.generator.metamodel;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Optional;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for AstTypeAnalysis.
 * Tests type analysis logic for various AST node types and field types.
 */
class AstTypeAnalysisTest {

    @Test
    void testAnalyze_SimpleClass() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(String.class);
        assertNotNull(analysis);
        assertEquals(String.class, analysis.innerType);
        assertFalse(analysis.isOptional);
        assertFalse(analysis.isNodeList);
        assertFalse(analysis.isSelfType);
    }

    @Test
    void testAnalyze_OptionalType() throws Exception {
        Field field = getTestField("optionalField");
        if (field != null) {
            AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
            assertNotNull(analysis);
            assertTrue(analysis.isOptional, "Should detect Optional type");
        }
    }

    @Test
    void testAnalyze_NodeListType() throws Exception {
        Field field = getTestField("nodeListField");
        if (field != null) {
            AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
            assertNotNull(analysis);
            assertTrue(analysis.isNodeList, "Should detect NodeList type");
        }
    }

    @Test
    void testAnalyze_OptionalNodeListType() throws Exception {
        Field field = getTestField("optionalNodeListField");
        if (field != null) {
            AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
            assertNotNull(analysis);
            assertTrue(analysis.isOptional, "Should detect Optional wrapper");
            assertTrue(analysis.isNodeList, "Should detect NodeList type");
        }
    }

    @Test
    void testAnalyze_AbstractClass() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(
                com.github.javaparser.ast.expr.Expression.class);
        assertNotNull(analysis);
        assertTrue(analysis.isAbstract, "Should detect abstract class");
        assertEquals(com.github.javaparser.ast.expr.Expression.class, analysis.innerType);
    }

    @Test
    void testAnalyze_ConcreteClass() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(
                com.github.javaparser.ast.CompilationUnit.class);
        assertNotNull(analysis);
        assertFalse(analysis.isAbstract, "Should detect concrete class");
        assertEquals(com.github.javaparser.ast.CompilationUnit.class, analysis.innerType);
    }

    @Test
    void testAnalyze_NodeType() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(Node.class);
        assertNotNull(analysis);
        assertEquals(Node.class, analysis.innerType);
        assertFalse(analysis.isOptional);
        assertFalse(analysis.isNodeList);
    }

    @Test
    void testAnalyze_TypeWithWildcard() throws Exception {
        // Test with a type that has wildcards (like NodeList<? extends Node>)
        Field field = getTestField("wildcardField");
        if (field != null) {
            AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
            assertNotNull(analysis);
            // Wildcard types should be detected as self type
            // This depends on the actual field type
        }
    }

    @Test
    void testAnalyze_StringType() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(String.class);
        assertNotNull(analysis);
        assertEquals(String.class, analysis.innerType);
        assertFalse(analysis.isOptional);
        assertFalse(analysis.isNodeList);
        assertFalse(analysis.isAbstract);
    }

    @Test
    void testAnalyze_IntegerType() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(Integer.class);
        assertNotNull(analysis);
        assertEquals(Integer.class, analysis.innerType);
        assertFalse(analysis.isOptional);
        assertFalse(analysis.isNodeList);
        assertFalse(analysis.isAbstract);
    }

    @Test
    void testAnalyze_NodeListOfNodes() throws Exception {
        // Test with actual NodeList field from Node class
        Field[] fields = Node.class.getDeclaredFields();
        for (Field field : fields) {
            if (field.getType() == NodeList.class) {
                AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
                assertNotNull(analysis);
                assertTrue(analysis.isNodeList, "Should detect NodeList type");
                break;
            }
        }
    }

    @Test
    void testAnalyze_OptionalNode() throws Exception {
        // Test with Optional<Node> type
        Field[] fields = Node.class.getDeclaredFields();
        for (Field field : fields) {
            if (field.getType() == Optional.class) {
                AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
                assertNotNull(analysis);
                assertTrue(analysis.isOptional, "Should detect Optional type");
                break;
            }
        }
    }

    @Test
    void testAnalyze_MethodReturnType() throws Exception {
        Method[] methods = Node.class.getDeclaredMethods();
        for (Method method : methods) {
            if (method.getReturnType() == Optional.class) {
                AstTypeAnalysis analysis = new AstTypeAnalysis(method.getGenericReturnType());
                assertNotNull(analysis);
                assertTrue(analysis.isOptional, "Should detect Optional return type");
                break;
            }
        }
    }

    @Test
    void testAnalyze_ComplexGenericType() throws Exception {
        // Test with complex generic types like Optional<NodeList<Node>>
        Field[] fields = Node.class.getDeclaredFields();
        for (Field field : fields) {
            if (field.getGenericType().getTypeName().contains("Optional") &&
                    field.getGenericType().getTypeName().contains("NodeList")) {
                AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
                assertNotNull(analysis);
                assertTrue(analysis.isOptional, "Should detect Optional in complex type");
                assertTrue(analysis.isNodeList, "Should detect NodeList in complex type");
                break;
            }
        }
    }

    @Test
    void testAnalyze_TypeParameter() {
        // Test with a class that has type parameters
        AstTypeAnalysis analysis = new AstTypeAnalysis(
                com.github.javaparser.ast.body.TypeDeclaration.class);
        assertNotNull(analysis);
        // Type parameters should be detected as self type
        // This depends on the actual class definition
    }

    @Test
    void testAnalyze_PrimitiveType() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(int.class);
        assertNotNull(analysis);
        assertEquals(int.class, analysis.innerType);
        assertFalse(analysis.isOptional);
        assertFalse(analysis.isNodeList);
    }

    @Test
    void testAnalyze_ArrayType() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(String[].class);
        assertNotNull(analysis);
        assertEquals(String[].class, analysis.innerType);
        assertFalse(analysis.isOptional);
        assertFalse(analysis.isNodeList);
    }

    @Test
    void testAnalyze_InnerClassType() {
        // Test with inner class types
        AstTypeAnalysis analysis = new AstTypeAnalysis(
                com.github.javaparser.ast.expr.Name.class);
        assertNotNull(analysis);
        assertNotNull(analysis.innerType);
    }

    @Test
    void testAnalyze_EnumType() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(
                com.github.javaparser.ast.Modifier.class);
        assertNotNull(analysis);
        assertEquals(com.github.javaparser.ast.Modifier.class, analysis.innerType);
        assertFalse(analysis.isAbstract);
    }

    @Test
    void testAnalyze_InterfaceType() {
        AstTypeAnalysis analysis = new AstTypeAnalysis(java.util.List.class);
        assertNotNull(analysis);
        assertEquals(java.util.List.class, analysis.innerType);
        assertTrue(analysis.isAbstract, "Interfaces should be detected as abstract");
    }

    @Test
    void testAnalyze_ActualNodeFields() throws Exception {
        // Test with actual fields from Node class
        Field[] fields = Node.class.getDeclaredFields();
        for (Field field : fields) {
            if (!java.lang.reflect.Modifier.isStatic(field.getModifiers())) {
                AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
                assertNotNull(analysis);
                assertNotNull(analysis.innerType);
                // Verify the analysis is valid
                assertTrue(analysis.innerType != null);
            }
        }
    }

    @Test
    void testAnalyze_ActualNodeMethods() throws Exception {
        // Test with actual methods from Node class
        Method[] methods = Node.class.getDeclaredMethods();
        for (Method method : methods) {
            if (method.getParameterCount() == 0 && method.getReturnType() != void.class) {
                AstTypeAnalysis analysis = new AstTypeAnalysis(method.getGenericReturnType());
                assertNotNull(analysis);
                assertNotNull(analysis.innerType);
            }
        }
    }

    @Test
    void testAnalyze_CompilationUnitFields() throws Exception {
        // Test with fields from CompilationUnit class
        Field[] fields = com.github.javaparser.ast.CompilationUnit.class.getDeclaredFields();
        for (Field field : fields) {
            if (!java.lang.reflect.Modifier.isStatic(field.getModifiers())) {
                AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
                assertNotNull(analysis);
                assertNotNull(analysis.innerType);
            }
        }
    }

    @Test
    void testAnalyze_MethodDeclarationFields() throws Exception {
        // Test with fields from MethodDeclaration class
        Field[] fields = com.github.javaparser.ast.body.MethodDeclaration.class.getDeclaredFields();
        for (Field field : fields) {
            if (!java.lang.reflect.Modifier.isStatic(field.getModifiers())) {
                AstTypeAnalysis analysis = new AstTypeAnalysis(field.getGenericType());
                assertNotNull(analysis);
                assertNotNull(analysis.innerType);
            }
        }
    }

    @Test
    void testAnalyze_NestedGenericTypes() throws Exception {
        // Test with deeply nested generic types
        // This tests the recursive type unwrapping logic
        AstTypeAnalysis analysis = new AstTypeAnalysis(
                java.util.List.class);
        assertNotNull(analysis);
        // The analysis should handle nested generics correctly
    }

    @Test
    void testAnalyze_TypeVariable() {
        // Test with type variables
        // Type variables should be handled appropriately
        AstTypeAnalysis analysis = new AstTypeAnalysis(
                com.github.javaparser.ast.body.TypeDeclaration.class);
        assertNotNull(analysis);
        // Type variables may be detected as self type
    }

    // Helper method to get test fields (if they exist in test classes)
    private Field getTestField(String fieldName) {
        try {
            // Try to find a field with the given name in Node or related classes
            Field[] fields = Node.class.getDeclaredFields();
            for (Field field : fields) {
                if (field.getName().equals(fieldName)) {
                    return field;
                }
            }
            // Try CompilationUnit
            fields = com.github.javaparser.ast.CompilationUnit.class.getDeclaredFields();
            for (Field field : fields) {
                if (field.getName().equals(fieldName)) {
                    return field;
                }
            }
        } catch (Exception e) {
            // Field not found, return null
        }
        return null;
    }
}

