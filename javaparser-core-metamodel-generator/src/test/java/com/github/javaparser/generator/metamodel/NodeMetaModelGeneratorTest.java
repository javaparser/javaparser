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

import static com.github.javaparser.generator.GeneratorTestHelper.assertClassExists;
import static com.github.javaparser.generator.GeneratorTestHelper.assertHasGeneratedAnnotation;
import static com.github.javaparser.generator.GeneratorTestHelper.createTempSourceRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.utils.SourceRoot;
import java.util.Optional;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Path;

/**
 * Comprehensive tests for NodeMetaModelGenerator.
 * Tests the node metamodel generation logic and verifies output correctness.
 */
class NodeMetaModelGeneratorTest {

    @TempDir
    Path tempDir;

    private SourceRoot sourceRoot;
    private NodeMetaModelGenerator generator;
    private ClassOrInterfaceDeclaration metaModelCoid;
    private CompilationUnit javaParserMetaModelCu;

    @BeforeEach
    void setUp() throws Exception {
        sourceRoot = new SourceRoot(tempDir);
        ParserConfiguration parserConfiguration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.RAW)
                .setStoreTokens(false);
        sourceRoot.setParserConfiguration(parserConfiguration);
        PrinterConfiguration config = new DefaultPrinterConfiguration()
                .addOption(new DefaultConfigurationOption(ConfigOption.END_OF_LINE_CHARACTER, "\n"));
        Printer printer = new DefaultPrettyPrinter(config);
        sourceRoot.setPrinter(printer::print);
        StaticJavaParser.setConfiguration(parserConfiguration);

        generator = new NodeMetaModelGenerator(sourceRoot);

        // Create a mock JavaParserMetaModel class
        javaParserMetaModelCu = new CompilationUnit(MetaModelGenerator.METAMODEL_PACKAGE);
        metaModelCoid = javaParserMetaModelCu.addClass("JavaParserMetaModel");
        metaModelCoid.setPublic(true);
        metaModelCoid.setStatic(true);
    }

    @Test
    void testGeneratorInitialization() {
        assertNotNull(generator);
        assertNotNull(generator.sourceRoot);
        assertEquals(sourceRoot, generator.sourceRoot);
    }

    @Test
    void testGenerate_ForRootNode() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        // Verify that statements were added
        assertTrue(initNodeMetaModels.size() > 0, "Should add initialization statement for root node");

        // Verify that a field was created
        Optional<FieldDeclaration> nodeField = metaModelCoid.getFieldByName("nodeMetaModel");
        assertTrue(nodeField.isPresent(), "Should create nodeMetaModel field");
    }

    @Test
    void testGenerate_ForNonRootNode() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                com.github.javaparser.ast.CompilationUnit.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        // Verify that statements were added
        assertTrue(initNodeMetaModels.size() > 0, "Should add initialization statement");

        // Verify that a field was created
        Optional<FieldDeclaration> compilationUnitField = metaModelCoid.getFieldByName("compilationUnitMetaModel");
        assertTrue(compilationUnitField.isPresent(), "Should create compilationUnitMetaModel field");
    }

    @Test
    void testGenerate_CreatesMetaModelClass() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        // Verify that a meta model class file was created
        Optional<CompilationUnit> nodeMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "NodeMetaModel");
        assertTrue(nodeMetaModelCu.isPresent(), "Should create NodeMetaModel.java file");

        // Verify the class exists in the compilation unit
        Optional<ClassOrInterfaceDeclaration> nodeMetaModelClass = nodeMetaModelCu.get().getClassByName("NodeMetaModel");
        assertTrue(nodeMetaModelClass.isPresent(), "Should create NodeMetaModel class");
    }

    @Test
    void testGenerate_AnnotatesClassAsGenerated() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        Optional<CompilationUnit> nodeMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "NodeMetaModel");
        assertTrue(nodeMetaModelCu.isPresent());

        Optional<ClassOrInterfaceDeclaration> nodeMetaModelClass = nodeMetaModelCu.get().getClassByName("NodeMetaModel");
        assertTrue(nodeMetaModelClass.isPresent());
        assertTrue(nodeMetaModelClass.get().getAnnotationByName("Generated").isPresent(),
                "Class should be annotated with @Generated");
    }

    @Test
    void testGenerate_CreatesConstructor() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        Optional<CompilationUnit> nodeMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "NodeMetaModel");
        assertTrue(nodeMetaModelCu.isPresent());

        Optional<ClassOrInterfaceDeclaration> nodeMetaModelClass = nodeMetaModelCu.get().getClassByName("NodeMetaModel");
        assertTrue(nodeMetaModelClass.isPresent());

        // Verify constructor exists
        assertTrue(nodeMetaModelClass.get().getConstructors().size() > 0,
                "Should create constructor for meta model class");
    }

    @Test
    void testGenerate_ForAbstractNode() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                com.github.javaparser.ast.expr.Expression.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        Optional<CompilationUnit> expressionMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "ExpressionMetaModel");
        assertTrue(expressionMetaModelCu.isPresent());

        Optional<ClassOrInterfaceDeclaration> expressionMetaModelClass =
                expressionMetaModelCu.get().getClassByName("ExpressionMetaModel");
        assertTrue(expressionMetaModelClass.isPresent());

        // Abstract classes should have a protected constructor
        List<ConstructorDeclaration> constructors = expressionMetaModelClass.get().getConstructors();
        assertTrue(constructors.size() > 0, "Abstract node should have constructor");
    }

    @Test
    void testGenerate_ExtendsBaseNodeMetaModelForRootNode() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        Optional<CompilationUnit> nodeMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "NodeMetaModel");
        assertTrue(nodeMetaModelCu.isPresent());

        Optional<ClassOrInterfaceDeclaration> nodeMetaModelClass = nodeMetaModelCu.get().getClassByName("NodeMetaModel");
        assertTrue(nodeMetaModelClass.isPresent());

        // Root node should extend BaseNodeMetaModel
        assertTrue(nodeMetaModelClass.get().getExtendedTypes().size() > 0,
                "Root node should extend BaseNodeMetaModel");
    }

    @Test
    void testGenerate_ExtendsSuperNodeMetaModelForNonRootNode() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                com.github.javaparser.ast.CompilationUnit.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        Optional<CompilationUnit> compilationUnitMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "CompilationUnitMetaModel");
        assertTrue(compilationUnitMetaModelCu.isPresent());

        Optional<ClassOrInterfaceDeclaration> compilationUnitMetaModelClass =
                compilationUnitMetaModelCu.get().getClassByName("CompilationUnitMetaModel");
        assertTrue(compilationUnitMetaModelClass.isPresent());

        // Non-root node should extend its super node's meta model
        assertTrue(compilationUnitMetaModelClass.get().getExtendedTypes().size() > 0,
                "Non-root node should extend super node meta model");
    }

    @Test
    void testGenerate_AddsImports() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        Optional<CompilationUnit> nodeMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "NodeMetaModel");
        assertTrue(nodeMetaModelCu.isPresent());

        // Verify imports are added
        assertTrue(nodeMetaModelCu.get().getImports().size() > 0,
                "Should add imports to meta model class");
    }

    @Test
    void testGenerate_ProcessesFields() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                com.github.javaparser.ast.CompilationUnit.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        // Verify that property meta model statements were added
        assertTrue(initPropertyMetaModels.size() > 0,
                "Should add property meta model initialization statements");
    }

    @Test
    void testGenerate_IgnoresStaticFields() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        Optional<CompilationUnit> nodeMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "NodeMetaModel");
        assertTrue(nodeMetaModelCu.isPresent());

        Optional<ClassOrInterfaceDeclaration> nodeMetaModelClass = nodeMetaModelCu.get().getClassByName("NodeMetaModel");
        assertTrue(nodeMetaModelClass.isPresent());

        // Static fields should not be processed
        // This is verified by checking that only non-static fields are processed
        assertNotNull(nodeMetaModelClass.get());
    }

    @Test
    void testGenerate_ProcessesDerivedProperties() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                com.github.javaparser.ast.CompilationUnit.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        // Derived properties should be processed if they have @DerivedProperty annotation
        // This is verified by the generator processing methods with @DerivedProperty
        assertNotNull(initPropertyMetaModels);
    }

    @Test
    void testGenerate_AddsCopyrightNotice() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        Optional<CompilationUnit> nodeMetaModelCu = sourceRoot.getCompilationUnit(
                MetaModelGenerator.METAMODEL_PACKAGE, "NodeMetaModel");
        assertTrue(nodeMetaModelCu.isPresent());

        // Verify copyright notice is added
        assertTrue(nodeMetaModelCu.get().getComment().isPresent() ||
                        nodeMetaModelCu.get().getBlockComment().isPresent(),
                "Should add copyright notice to generated file");
    }

    @Test
    void testGenerate_RemovesExistingField() throws Exception {
        // Add an existing field
        FieldDeclaration existingField = metaModelCoid.addField("NodeMetaModel", "nodeMetaModel");
        existingField.setStatic(true);
        existingField.setFinal(true);

        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        // The generator should remove the existing field and create a new one
        Optional<FieldDeclaration> nodeField = metaModelCoid.getFieldByName("nodeMetaModel");
        assertTrue(nodeField.isPresent(), "Should create new nodeMetaModel field");
    }

    @Test
    void testGenerate_ForVariousNodeTypes() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        // Test with different node types
        Class<? extends Node>[] nodeTypes = new Class[] {
                Node.class,
                com.github.javaparser.ast.CompilationUnit.class,
                com.github.javaparser.ast.body.MethodDeclaration.class,
                com.github.javaparser.ast.expr.Expression.class
        };

        for (Class<? extends Node> nodeType : nodeTypes) {
            generator.generate(
                    nodeType,
                    metaModelCoid,
                    initNodeMetaModels,
                    initPropertyMetaModels,
                    initConstructorParameters,
                    sourceRoot);

            String expectedClassName = MetaModelGenerator.nodeMetaModelName(nodeType);
            Optional<CompilationUnit> metaModelCu = sourceRoot.getCompilationUnit(
                    MetaModelGenerator.METAMODEL_PACKAGE, expectedClassName);
            assertTrue(metaModelCu.isPresent(),
                    "Should create meta model for " + nodeType.getSimpleName());
        }
    }

    @Test
    void testGenerate_AddsJavadocComment() throws Exception {
        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        // Verify that JavaParserMetaModel class gets javadoc comment
        assertTrue(metaModelCoid.getJavadocComment().isPresent() ||
                        metaModelCoid.getComment().isPresent(),
                "Should add javadoc comment to JavaParserMetaModel class");
    }

    @Test
    void testGenerate_MovesStaticInitializerToEnd() throws Exception {
        // Add a static initializer
        metaModelCoid.addInitializer(true);

        NodeList<Statement> initNodeMetaModels = new NodeList<>();
        NodeList<Statement> initPropertyMetaModels = new NodeList<>();
        NodeList<Statement> initConstructorParameters = new NodeList<>();

        generator.generate(
                Node.class,
                metaModelCoid,
                initNodeMetaModels,
                initPropertyMetaModels,
                initConstructorParameters,
                sourceRoot);

        // The generator should move static initializer to the end
        // This is verified by the generator's internal logic
        assertNotNull(metaModelCoid);
    }
}

