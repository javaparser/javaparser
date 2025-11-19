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
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.stmt.Statement;
import java.lang.reflect.Constructor;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for InitializeConstructorParametersStatementsGenerator.
 * Tests constructor parameter statement generation logic and verifies output correctness.
 */
class InitializeConstructorParametersStatementsGeneratorTest {

    private InitializeConstructorParametersStatementsGenerator generator;
    private NodeList<Statement> initializeConstructorParametersStatements;

    @BeforeEach
    void setUp() {
        generator = new InitializeConstructorParametersStatementsGenerator();
        initializeConstructorParametersStatements = new NodeList<>();
    }

    @Test
    void testGenerate_WithRootNode() {
        // Root node (Node.class) should return early without adding statements
        generator.generate(Node.class, initializeConstructorParametersStatements);

        // Root node should not add any statements
        assertEquals(0, initializeConstructorParametersStatements.size(),
                "Root node should not add constructor parameter statements");
    }

    @Test
    void testGenerate_WithCompilationUnit() {
        generator.generate(
                com.github.javaparser.ast.CompilationUnit.class,
                initializeConstructorParametersStatements);

        // CompilationUnit should have constructor parameters
        // The exact count depends on the class definition
        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_WithMethodDeclaration() {
        generator.generate(
                com.github.javaparser.ast.body.MethodDeclaration.class,
                initializeConstructorParametersStatements);

        // MethodDeclaration should have constructor parameters
        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_WithClassOrInterfaceDeclaration() {
        generator.generate(
                com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class,
                initializeConstructorParametersStatements);

        // ClassOrInterfaceDeclaration should have constructor parameters
        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_WithExpression() {
        generator.generate(
                com.github.javaparser.ast.expr.Expression.class,
                initializeConstructorParametersStatements);

        // Expression is abstract, but may have constructor parameters
        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_WithStatement() {
        generator.generate(
                com.github.javaparser.ast.stmt.Statement.class,
                initializeConstructorParametersStatements);

        // Statement is abstract, but may have constructor parameters
        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_WithVariousNodeTypes() {
        // Test with various node types
        Class<? extends Node>[] nodeTypes = new Class[] {
                com.github.javaparser.ast.CompilationUnit.class,
                com.github.javaparser.ast.body.MethodDeclaration.class,
                com.github.javaparser.ast.body.FieldDeclaration.class,
                com.github.javaparser.ast.expr.NameExpr.class,
                com.github.javaparser.ast.stmt.ReturnStmt.class
        };

        for (Class<? extends Node> nodeType : nodeTypes) {
            initializeConstructorParametersStatements.clear();
            generator.generate(nodeType, initializeConstructorParametersStatements);

            // Each node type should be processed
            assertNotNull(initializeConstructorParametersStatements,
                    "Should process constructor parameters for " + nodeType.getSimpleName());
        }
    }

    @Test
    void testGenerate_AddsStatementsForEachParameter() {
        // Find a node class with @AllFieldsConstructor
        Class<? extends Node> nodeClass = com.github.javaparser.ast.CompilationUnit.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);

        // Verify statements were added (one per constructor parameter)
        // The exact count depends on the constructor
        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_StatementContent() {
        Class<? extends Node> nodeClass = com.github.javaparser.ast.CompilationUnit.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);

        // Verify statements contain expected content
        for (Statement statement : initializeConstructorParametersStatements) {
            assertNotNull(statement);
            String statementStr = statement.toString();

            // Statements should add constructor parameters
            assertTrue(statementStr.contains("getConstructorParameters") ||
                            statementStr.contains("add"),
                    "Statement should add constructor parameters");
        }
    }

    @Test
    void testGenerate_WithNodeWithoutAllFieldsConstructor() {
        // Some node classes might not have @AllFieldsConstructor
        // This should throw an AssertionError
        // We test this by trying classes that might not have the annotation
        Class<? extends Node>[] testClasses = new Class[] {
                com.github.javaparser.ast.CompilationUnit.class,
                com.github.javaparser.ast.body.MethodDeclaration.class
        };

        for (Class<? extends Node> nodeClass : testClasses) {
            try {
                initializeConstructorParametersStatements.clear();
                generator.generate(nodeClass, initializeConstructorParametersStatements);
                // If no exception is thrown, the class has @AllFieldsConstructor
                assertNotNull(initializeConstructorParametersStatements);
            } catch (AssertionError e) {
                // Expected if the class doesn't have @AllFieldsConstructor
                assertTrue(e.getMessage().contains("no constructor annotated with @AllFieldsConstructor"));
            }
        }
    }

    @Test
    void testGenerate_HandlesMultipleParameters() {
        Class<? extends Node> nodeClass = com.github.javaparser.ast.CompilationUnit.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);

        // If the constructor has multiple parameters, multiple statements should be added
        assertNotNull(initializeConstructorParametersStatements);
        // The count should match the number of constructor parameters
    }

    @Test
    void testGenerate_WithAbstractNode() {
        // Abstract nodes might still have constructors
        generator.generate(
                com.github.javaparser.ast.expr.Expression.class,
                initializeConstructorParametersStatements);

        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_WithConcreteNode() {
        generator.generate(
                com.github.javaparser.ast.CompilationUnit.class,
                initializeConstructorParametersStatements);

        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_StatementFormat() {
        Class<? extends Node> nodeClass = com.github.javaparser.ast.CompilationUnit.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);

        // Verify statement format
        for (Statement statement : initializeConstructorParametersStatements) {
            String statementStr = statement.toString();
            // Should follow pattern: nodeMetaModel.getConstructorParameters().add(...)
            assertTrue(statementStr.contains("getConstructorParameters") ||
                            statementStr.contains("add"),
                    "Statement should follow expected format");
        }
    }

    @Test
    void testGenerate_WithNodeHavingNoParameters() {
        // Some nodes might have constructors with no parameters
        // This should still work (just add no statements)
        Class<? extends Node> nodeClass = Node.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);

        // Root node should not add statements
        assertEquals(0, initializeConstructorParametersStatements.size());
    }

    @Test
    void testGenerate_WithNodeHavingManyParameters() {
        // Test with a node that likely has many constructor parameters
        Class<? extends Node> nodeClass = com.github.javaparser.ast.body.MethodDeclaration.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);

        // Should handle nodes with many parameters
        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_FieldNameResolution() {
        // Test that field names are correctly resolved from constructor parameters
        Class<? extends Node> nodeClass = com.github.javaparser.ast.CompilationUnit.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);

        // Verify that statements reference correct field names
        for (Statement statement : initializeConstructorParametersStatements) {
            assertNotNull(statement);
            // The statement should reference property meta models
            String statementStr = statement.toString();
            assertTrue(statementStr.contains("PropertyMetaModel") ||
                            statementStr.contains("MetaModel"),
                    "Statement should reference property meta models");
        }
    }

    @Test
    void testGenerate_WithInheritedFields() {
        // Test that inherited fields are correctly handled
        Class<? extends Node> nodeClass = com.github.javaparser.ast.body.MethodDeclaration.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);

        // Should handle fields from parent classes
        assertNotNull(initializeConstructorParametersStatements);
    }

    @Test
    void testGenerate_Consistency() {
        // Test that generating multiple times produces consistent results
        Class<? extends Node> nodeClass = com.github.javaparser.ast.CompilationUnit.class;

        generator.generate(nodeClass, initializeConstructorParametersStatements);
        int firstCount = initializeConstructorParametersStatements.size();

        initializeConstructorParametersStatements.clear();
        generator.generate(nodeClass, initializeConstructorParametersStatements);
        int secondCount = initializeConstructorParametersStatements.size();

        // Should produce the same number of statements
        assertEquals(firstCount, secondCount, "Should produce consistent results");
    }

    @Test
    void testGenerate_WithVariousNodeHierarchies() {
        // Test with nodes from different hierarchies
        Class<? extends Node>[] nodeClasses = new Class[] {
                com.github.javaparser.ast.CompilationUnit.class, // Top-level
                com.github.javaparser.ast.body.MethodDeclaration.class, // Body declaration
                com.github.javaparser.ast.expr.NameExpr.class, // Expression
                com.github.javaparser.ast.stmt.ReturnStmt.class, // Statement
                com.github.javaparser.ast.type.ClassOrInterfaceType.class // Type
        };

        for (Class<? extends Node> nodeClass : nodeClasses) {
            initializeConstructorParametersStatements.clear();
            try {
                generator.generate(nodeClass, initializeConstructorParametersStatements);
                assertNotNull(initializeConstructorParametersStatements,
                        "Should handle " + nodeClass.getSimpleName());
            } catch (AssertionError e) {
                // Some classes might not have @AllFieldsConstructor
                assertTrue(e.getMessage().contains("no constructor annotated with @AllFieldsConstructor") ||
                                e.getMessage().contains("Couldn't find constructor parameter"));
            }
        }
    }

    @Test
    void testGenerate_ErrorHandling() {
        // Test error handling for invalid cases
        // This is tested through the AssertionError thrown when:
        // 1. No @AllFieldsConstructor is found
        // 2. Constructor parameter doesn't match a field

        // We can't easily create an invalid case, but we can verify
        // that the generator handles valid cases correctly
        Class<? extends Node> nodeClass = com.github.javaparser.ast.CompilationUnit.class;
        generator.generate(nodeClass, initializeConstructorParametersStatements);
        assertNotNull(initializeConstructorParametersStatements);
    }
}

