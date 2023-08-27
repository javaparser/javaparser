/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclarationTest;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.CodeGenerationUtils;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Optional;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.*;

class JavaParserFieldDeclarationTest implements ResolvedFieldDeclarationTest {

    @Test
    void whenTypeSolverIsNullShouldThrowIllegalArgumentException() {
        CompilationUnit compilationUnit = StaticJavaParser.parse("class A {String s;}");
        VariableDeclarator variableDeclarator = compilationUnit.findFirst(FieldDeclaration.class).get()
                .getVariable(0);
        assertThrows(IllegalArgumentException.class,
                () -> new JavaParserFieldDeclaration(variableDeclarator, null));
    }
    
    @Test
    void verifyIsVolatileVariableDeclarationFromJavaParser() {
        CompilationUnit compilationUnit = StaticJavaParser.parse("class A {volatile int counter = 0;}");
        FieldDeclaration fieldDeclaration = compilationUnit.findFirst(FieldDeclaration.class).get();
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        ResolvedFieldDeclaration rfd = new JavaParserFieldDeclaration(fieldDeclaration.getVariable(0), reflectionTypeSolver);
        assertTrue(rfd.isVolatile());
    }
    
    @Test
    void verifyIsNotVolatileVariableDeclarationFromJavaParser() {
        CompilationUnit compilationUnit = StaticJavaParser.parse("class A {int counter = 0;}");
        FieldDeclaration fieldDeclaration = compilationUnit.findFirst(FieldDeclaration.class).get();
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        ResolvedFieldDeclaration rfd = new JavaParserFieldDeclaration(fieldDeclaration.getVariable(0), reflectionTypeSolver);
        assertFalse(rfd.isVolatile());
    }

    @Test
    void checkModifiersOnInterfaceFields() throws IOException {
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        Path rootDir = CodeGenerationUtils.mavenModuleRoot(JavaParserFieldDeclarationTest.class).resolve("src/test/java/com/github/javaparser/symbolsolver/testingclasses");
        CompilationUnit cu = parse(rootDir.resolve("InterfaceWithFields.java"));
        FieldDeclaration field1 = cu.findAll(FieldDeclaration.class).get(0);

        ResolvedFieldDeclaration resolvedField1 = new JavaParserFieldDeclaration(field1.getVariable(0), reflectionTypeSolver);

        assertTrue(resolvedField1.hasModifier(Modifier.Keyword.PUBLIC));
        assertTrue(resolvedField1.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(resolvedField1.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.ABSTRACT));

        FieldDeclaration field2 = cu.findAll(FieldDeclaration.class).get(1);

        ResolvedFieldDeclaration resolvedField2 = new JavaParserFieldDeclaration(field2.getVariable(0), reflectionTypeSolver);

        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.PUBLIC));
        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(resolvedField2.hasModifier(Modifier.Keyword.ABSTRACT));
    }

    @Test
    void checkModifiersOnClassFields() throws IOException {
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        Path rootDir = CodeGenerationUtils.mavenModuleRoot(JavaParserFieldDeclarationTest.class).resolve("src/test/java/com/github/javaparser/symbolsolver/testingclasses");
        CompilationUnit cu = parse(rootDir.resolve("ClassWithFields.java"));
        FieldDeclaration field1 = cu.findAll(FieldDeclaration.class).get(0);
        ResolvedFieldDeclaration resolvedField1 = new JavaParserFieldDeclaration(field1.getVariable(0), reflectionTypeSolver);

        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.PUBLIC));
        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.ABSTRACT));

        FieldDeclaration field2 = cu.findAll(FieldDeclaration.class).get(1);
        ResolvedFieldDeclaration resolvedField2 = new JavaParserFieldDeclaration(field2.getVariable(0), reflectionTypeSolver);

        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.PUBLIC));
        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(resolvedField2.hasModifier(Modifier.Keyword.ABSTRACT));
    }
    
    //
    //  Initialize ResolvedFieldDeclarationTest
    //

    private static ResolvedFieldDeclaration createResolvedFieldDeclaration(boolean isStatic) {
        String code = isStatic ? "class A {static String s;}" : "class A {String s;}";
        FieldDeclaration fieldDeclaration = StaticJavaParser.parse(code)
                .findFirst(FieldDeclaration.class).get();
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        return new JavaParserFieldDeclaration(fieldDeclaration.getVariable(0), reflectionTypeSolver);
    }

    @Override
    public ResolvedFieldDeclaration createValue() {
        return createResolvedFieldDeclaration(false);
    }

    @Override
    public ResolvedFieldDeclaration createStaticValue() {
        return createResolvedFieldDeclaration(true);
    }

    @Override
    public Optional<Node> getWrappedDeclaration(AssociableToAST associableToAST) {
        return Optional.of(
                safeCast(associableToAST, JavaParserFieldDeclaration.class).getWrappedNode()
        );
    }

    @Override
    public String getCanonicalNameOfExpectedType(ResolvedValueDeclaration resolvedDeclaration) {
        return String.class.getCanonicalName();
    }

}
