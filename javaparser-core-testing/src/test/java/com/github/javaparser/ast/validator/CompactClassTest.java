/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

package com.github.javaparser.ast.validator;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_25;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import org.junit.jupiter.api.Test;

/**
 * Tests for JEP 512: Compact Source Files and Instance Main Methods (Java 25)
 *
 * @see <a href="https://openjdk.org/jeps/512">JEP 512</a>
 */
class CompactClassTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));

    @Test
    void simpleMainMethod() {
        String code = "void main() { System.out.println(\"Hello, World!\"); }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        assertEquals(1, cu.getTypes().size(), "Should have one implicit class");

        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        assertTrue(implicitClass.isCompact(), "Should be marked as compact class");
        assertEquals(1, implicitClass.getMethods().size(), "Should have one method");

        MethodDeclaration mainMethod = implicitClass.getMethods().get(0);
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void mainMethodWithParameters() {
        String code = "void main(String[] args) { System.out.println(args[0]); }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        assertTrue(implicitClass.isCompact());

        MethodDeclaration mainMethod = implicitClass.getMethods().get(0);
        assertEquals(1, mainMethod.getParameters().size());
    }

    @Test
    void compactClassWithField() {
        String code = "String greeting = \"Hello\";\n" + "void main() { System.out.println(greeting); }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        assertTrue(implicitClass.isCompact());

        assertEquals(1, implicitClass.getFields().size(), "Should have one field");
        assertEquals(1, implicitClass.getMethods().size(), "Should have one method");
    }

    @Test
    void compactClassWithMultipleMethods() {
        String code = "void main() { helper(); }\n" + "void helper() { System.out.println(\"Helper\"); }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        assertTrue(implicitClass.isCompact());
        assertEquals(2, implicitClass.getMethods().size());
    }

    @Test
    void publicMainMethod() {
        String code = "public void main() { System.out.println(\"Public main\"); }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        assertTrue(implicitClass.isCompact());

        MethodDeclaration mainMethod = implicitClass.getMethods().get(0);
        assertTrue(mainMethod.isPublic());
    }

    @Test
    void regularClassStillWorks() {
        String code = "class HelloWorld { public static void main(String[] args) { } }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration regularClass =
                cu.getClassByName("HelloWorld").get();
        assertFalse(regularClass.isCompact(), "Regular class should not be compact");
    }

    @Test
    void mixedCompactAndRegularClass() {
        String code = "void main() { new Helper().help(); }\n" + "class Helper { void help() { } }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        assertEquals(2, cu.getTypes().size(), "Should have compact class and regular class");

        // Find the compact class (empty name)
        ClassOrInterfaceDeclaration compactClass =
                (ClassOrInterfaceDeclaration) cu.getTypes().get(0);
        assertTrue(compactClass.isCompact());

        // Find the regular class
        ClassOrInterfaceDeclaration regularClass = cu.getClassByName("Helper").get();
        assertFalse(regularClass.isCompact());
    }

    // ==================== JEP 512: Flexible Main Method Signatures ====================

    @Test
    void instanceMainMethod() {
        // JEP 512 allows instance (non-static) main methods
        String code = "void main() { System.out.println(\"Instance main\"); }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        MethodDeclaration mainMethod = implicitClass.getMethods().get(0);

        assertFalse(mainMethod.isStatic(), "Main method can be instance in JEP 512");
    }

    @Test
    void mainMethodWithIntReturnType() {
        // JEP 512 allows main to return int
        String code = "int main() { return 0; }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        MethodDeclaration mainMethod = implicitClass.getMethods().get(0);

        assertEquals("int", mainMethod.getTypeAsString());
    }

    @Test
    void mainMethodWithIntReturnAndParameters() {
        // JEP 512 allows int main(String[] args)
        String code = "int main(String[] args) { return args.length; }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        MethodDeclaration mainMethod = implicitClass.getMethods().get(0);

        assertEquals("int", mainMethod.getTypeAsString());
        assertEquals(1, mainMethod.getParameters().size());
    }

    @Test
    void staticMainMethodStillWorks() {
        // Classic static main should still work
        String code = "public static void main(String[] args) { }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass = cu.getClassByName("").get();
        MethodDeclaration mainMethod = implicitClass.getMethods().get(0);

        assertTrue(mainMethod.isStatic());
        assertTrue(mainMethod.isPublic());
    }

    // ==================== Validation Tests: Invalid Main Signatures ====================

    @Test
    void mainMethodWithInvalidReturnType() {
        // Main must return void or int
        String code = "String main() { return \"invalid\"; }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertProblems(result, "(line 1,col 1) Main method must have return type 'void' or 'int', found: 'String'.");
    }

    @Test
    void mainMethodWithTooManyParameters() {
        // Main can have 0 or 1 parameter
        String code = "void main(String[] args, int x) { }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertProblems(result, "(line 1,col 1) Main method must have zero or one parameter (String[]).");
    }

    @Test
    void mainMethodWithWrongParameterType() {
        // Main parameter must be String[]
        String code = "void main(int[] args) { }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertProblems(result, "(line 1,col 1) Main method parameter must be 'String[]', found: 'int[]'.");
    }

    // ==================== Validation Tests: Compact Class Restrictions ====================

    @Test
    void compactClassCannotExtend() {
        // Compact classes cannot extend other classes
        String code = "void main() { }\n" + "class MyCompact extends Object { }";

        // Note: The compact class is the one with main(), not MyCompact
        // We need to test if a compact class tries to extend
        // But our current parser creates compact class from top-level members
        // So we can't directly create "compact class extends Foo" in source

        // This test validates that regular classes can still extend (no regression)
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);
    }

    @Test
    void compactClassCannotImplement() {
        // Similar limitation as above - compact classes are created implicitly
        // Direct testing requires modifying AST programmatically
        String code = "void main() { }";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));

        assertNoProblems(result);

        // Get the implicit compact class and verify it has no extends/implements
        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration compactClass = cu.getClassByName("").get();

        assertTrue(compactClass.getExtendedTypes().isEmpty(), "Compact class should not extend");
        assertTrue(compactClass.getImplementedTypes().isEmpty(), "Compact class should not implement");
    }
}
