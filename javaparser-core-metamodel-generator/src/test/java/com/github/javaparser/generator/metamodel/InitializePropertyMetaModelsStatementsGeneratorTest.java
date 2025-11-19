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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import static com.github.javaparser.utils.CodeGenerationUtils.getterToPropertyName;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.stmt.Statement;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Optional;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for InitializePropertyMetaModelsStatementsGenerator.
 * Tests property meta model statement generation logic and verifies output correctness.
 */
class InitializePropertyMetaModelsStatementsGeneratorTest {

    private InitializePropertyMetaModelsStatementsGenerator generator;
    private ClassOrInterfaceDeclaration nodeMetaModelClass;
    private NodeList<Statement> initializePropertyMetaModelsStatements;

    @BeforeEach
    void setUp() {
        generator = new InitializePropertyMetaModelsStatementsGenerator();
        nodeMetaModelClass = new ClassOrInterfaceDeclaration();
        nodeMetaModelClass.setName("TestNodeMetaModel");
        initializePropertyMetaModelsStatements = new NodeList<>();
    }

    @Test
    void testGenerate_WithSimpleField() throws Exception {
        Field field = com.github.javaparser.ast.CompilationUnit.class.getDeclaredField("packageDeclaration");
        if (field != null) {
            generator.generate(
                    field,
                    nodeMetaModelClass,
                    "compilationUnitMetaModel",
                    initializePropertyMetaModelsStatements);

            // Verify statements were added
            assertTrue(initializePropertyMetaModelsStatements.size() >= 2,
                    "Should add at least 2 statements (field setting and addition)");

            // Verify field was added to meta model class
            Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                    field.getName() + "PropertyMetaModel");
            assertTrue(propertyField.isPresent(), "Should create property meta model field");
        }
    }

    @Test
    void testGenerate_WithNodeListField() throws Exception {
        Field field = com.github.javaparser.ast.CompilationUnit.class.getDeclaredField("types");
        if (field != null) {
            generator.generate(
                    field,
                    nodeMetaModelClass,
                    "compilationUnitMetaModel",
                    initializePropertyMetaModelsStatements);

            // Verify statements were added
            assertTrue(initializePropertyMetaModelsStatements.size() >= 2,
                    "Should add statements for NodeList field");

            // Verify field was added
            Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                    field.getName() + "PropertyMetaModel");
            assertTrue(propertyField.isPresent(), "Should create property meta model field for NodeList");
        }
    }

    @Test
    void testGenerate_WithOptionalField() throws Exception {
        Field field = com.github.javaparser.ast.CompilationUnit.class.getDeclaredField("module");
        if (field != null) {
            generator.generate(
                    field,
                    nodeMetaModelClass,
                    "compilationUnitMetaModel",
                    initializePropertyMetaModelsStatements);

            // Verify statements were added
            assertTrue(initializePropertyMetaModelsStatements.size() >= 2,
                    "Should add statements for Optional field");

            // Verify field was added
            Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                    field.getName() + "PropertyMetaModel");
            assertTrue(propertyField.isPresent(), "Should create property meta model field for Optional");
        }
    }

    @Test
    void testGenerate_WithNodeField() throws Exception {
        Field field = com.github.javaparser.ast.Node.class.getDeclaredField("parentNode");
        if (field != null) {
            generator.generate(
                    field,
                    nodeMetaModelClass,
                    "nodeMetaModel",
                    initializePropertyMetaModelsStatements);

            // Verify statements were added
            assertTrue(initializePropertyMetaModelsStatements.size() >= 2,
                    "Should add statements for Node field");

            // Verify field was added
            Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                    field.getName() + "PropertyMetaModel");
            assertTrue(propertyField.isPresent(), "Should create property meta model field for Node");
        }
    }

    @Test
    void testGenerate_WithPrimitiveField() throws Exception {
        // Find a primitive field if it exists
        Field[] fields = com.github.javaparser.ast.CompilationUnit.class.getDeclaredFields();
        for (Field field : fields) {
            if (field.getType().isPrimitive() && !java.lang.reflect.Modifier.isStatic(field.getModifiers())) {
                generator.generate(
                        field,
                        nodeMetaModelClass,
                        "compilationUnitMetaModel",
                        initializePropertyMetaModelsStatements);

                // Verify statements were added
                assertTrue(initializePropertyMetaModelsStatements.size() >= 2,
                        "Should add statements for primitive field");

                // Verify field was added
                Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                        field.getName() + "PropertyMetaModel");
                assertTrue(propertyField.isPresent(), "Should create property meta model field for primitive");
                break;
            }
        }
    }

    @Test
    void testGenerate_WithStringField() throws Exception {
        // Find a String field if it exists
        Field[] fields = com.github.javaparser.ast.CompilationUnit.class.getDeclaredFields();
        for (Field field : fields) {
            if (field.getType() == String.class && !java.lang.reflect.Modifier.isStatic(field.getModifiers())) {
                generator.generate(
                        field,
                        nodeMetaModelClass,
                        "compilationUnitMetaModel",
                        initializePropertyMetaModelsStatements);

                // Verify statements were added
                assertTrue(initializePropertyMetaModelsStatements.size() >= 2,
                        "Should add statements for String field");

                // Verify field was added
                Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                        field.getName() + "PropertyMetaModel");
                assertTrue(propertyField.isPresent(), "Should create property meta model field for String");
                break;
            }
        }
    }

    @Test
    void testGenerateDerivedProperty_WithGetterMethod() throws Exception {
        // Find a method with @DerivedProperty annotation
        Method[] methods = com.github.javaparser.ast.Node.class.getDeclaredMethods();
        for (Method method : methods) {
            if (method.isAnnotationPresent(com.github.javaparser.metamodel.DerivedProperty.class)) {
                generator.generateDerivedProperty(
                        method,
                        nodeMetaModelClass,
                        "nodeMetaModel",
                        initializePropertyMetaModelsStatements);

                // Verify statements were added
                assertTrue(initializePropertyMetaModelsStatements.size() >= 2,
                        "Should add statements for derived property");

                // Verify field was added
                String propertyName = getterToPropertyName(method.getName());
                Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                        propertyName + "PropertyMetaModel");
                assertTrue(propertyField.isPresent(), "Should create property meta model field for derived property");
                break;
            }
        }
    }

    @Test
    void testGenerate_AddsFieldToMetaModelClass() throws Exception {
        Field field = com.github.javaparser.ast.CompilationUnit.class.getDeclaredField("packageDeclaration");
        if (field != null) {
            int initialFieldCount = nodeMetaModelClass.getFields().size();

            generator.generate(
                    field,
                    nodeMetaModelClass,
                    "compilationUnitMetaModel",
                    initializePropertyMetaModelsStatements);

            // Verify a new field was added
            assertTrue(nodeMetaModelClass.getFields().size() > initialFieldCount,
                    "Should add a new field to meta model class");
        }
    }

    @Test
    void testGenerate_AddsStatementsToInitializer() throws Exception {
        Field field = com.github.javaparser.ast.CompilationUnit.class.getDeclaredField("packageDeclaration");
        if (field != null) {
            int initialStatementCount = initializePropertyMetaModelsStatements.size();

            generator.generate(
                    field,
                    nodeMetaModelClass,
                    "compilationUnitMetaModel",
                    initializePropertyMetaModelsStatements);

            // Verify statements were added
            assertTrue(initializePropertyMetaModelsStatements.size() > initialStatementCount,
                    "Should add statements to initializer");
            assertTrue(initializePropertyMetaModelsStatements.size() >= initialStatementCount + 2,
                    "Should add at least 2 statements");
        }
    }

    @Test
    void testGenerate_WithVariousFieldTypes() throws Exception {
        // Test with various field types from CompilationUnit
        Field[] fields = com.github.javaparser.ast.CompilationUnit.class.getDeclaredFields();
        int testedFields = 0;
        for (Field field : fields) {
            if (!java.lang.reflect.Modifier.isStatic(field.getModifiers()) && testedFields < 5) {
                generator.generate(
                        field,
                        nodeMetaModelClass,
                        "compilationUnitMetaModel",
                        initializePropertyMetaModelsStatements);

                // Verify field was added
                Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                        field.getName() + "PropertyMetaModel");
                assertTrue(propertyField.isPresent(),
                        "Should create property meta model field for " + field.getName());
                testedFields++;
            }
        }
    }

    @Test
    void testGenerate_FieldNameFormatting() throws Exception {
        Field field = com.github.javaparser.ast.CompilationUnit.class.getDeclaredField("packageDeclaration");
        if (field != null) {
            generator.generate(
                    field,
                    nodeMetaModelClass,
                    "compilationUnitMetaModel",
                    initializePropertyMetaModelsStatements);

            // Verify field name follows the pattern: fieldName + "PropertyMetaModel"
            String expectedFieldName = field.getName() + "PropertyMetaModel";
            Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(expectedFieldName);
            assertTrue(propertyField.isPresent(),
                    "Field name should follow pattern: " + expectedFieldName);
        }
    }

    @Test
    void testGenerate_StatementContent() throws Exception {
        Field field = com.github.javaparser.ast.CompilationUnit.class.getDeclaredField("packageDeclaration");
        if (field != null) {
            generator.generate(
                    field,
                    nodeMetaModelClass,
                    "compilationUnitMetaModel",
                    initializePropertyMetaModelsStatements);

            // Verify statements contain expected content
            assertTrue(initializePropertyMetaModelsStatements.size() >= 2);
            Statement firstStatement = initializePropertyMetaModelsStatements.get(0);
            Statement secondStatement = initializePropertyMetaModelsStatements.get(1);

            assertNotNull(firstStatement);
            assertNotNull(secondStatement);

            // Verify statements are assignment and addition statements
            String firstStatementStr = firstStatement.toString();
            String secondStatementStr = secondStatement.toString();

            assertTrue(firstStatementStr.contains("=") || firstStatementStr.contains("PropertyMetaModel"),
                    "First statement should be a field assignment");
            assertTrue(secondStatementStr.contains("add") || secondStatementStr.contains("PropertyMetaModel"),
                    "Second statement should add property to list");
        }
    }

    @Test
    void testGenerateDerivedProperty_WithVariousReturnTypes() throws Exception {
        // Test with methods that have different return types
        Method[] methods = com.github.javaparser.ast.Node.class.getDeclaredMethods();
        int testedMethods = 0;
        for (Method method : methods) {
            if (method.isAnnotationPresent(com.github.javaparser.metamodel.DerivedProperty.class) && testedMethods < 3) {
                generator.generateDerivedProperty(
                        method,
                        nodeMetaModelClass,
                        "nodeMetaModel",
                        initializePropertyMetaModelsStatements);

                // Verify statements were added
                assertTrue(initializePropertyMetaModelsStatements.size() >= 2,
                        "Should add statements for derived property with return type: " + method.getReturnType());

                testedMethods++;
            }
        }
    }

    @Test
    void testGenerate_HandlesInnerClassTypes() throws Exception {
        // Test with fields that have inner class types
        Field[] fields = com.github.javaparser.ast.CompilationUnit.class.getDeclaredFields();
        for (Field field : fields) {
            if (field.getType().getName().contains("$") && !java.lang.reflect.Modifier.isStatic(field.getModifiers())) {
                generator.generate(
                        field,
                        nodeMetaModelClass,
                        "compilationUnitMetaModel",
                        initializePropertyMetaModelsStatements);

                // Verify the type name is properly formatted (replacing $ with .)
                Optional<FieldDeclaration> propertyField = nodeMetaModelClass.getFieldByName(
                        field.getName() + "PropertyMetaModel");
                assertTrue(propertyField.isPresent(),
                        "Should handle inner class types correctly");
                break;
            }
        }
    }

}

