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

package com.github.javaparser;

import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.junit.jupiter.api.Test;

/**
 * Tests for Java 25 Compact Classes feature (JEP 512)
 * These tests implement the specific feedback from Johannes Coetzee's review.
 */
class CompactClassTest {

    private static final ParserConfiguration.LanguageLevel JAVA_25 = ParserConfiguration.LanguageLevel.JAVA_25;
    private static final ParserConfiguration.LanguageLevel JAVA_24 = ParserConfiguration.LanguageLevel.JAVA_24;

    @Test
    void testCompactClassParsing() {
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));

        // Simple main method test
        String code = "void main() { System.out.println(\"Hello\"); }";
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
        assertTrue(result.isSuccessful());
    }

    @Test
    void testInstanceMainMethod() {
        // JEP 512 allows instance (non-static) main methods
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));
        String code = "void main() { System.out.println(\"Instance main\"); }";
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration implicitClass =
                cu.getClassByName("$CompactClass").get();
        assertNotNull(implicitClass);
        assertTrue(implicitClass.getIsCompact());
    }

    @Test
    void testInvalidMainMethodReturnType() {
        // JEP 512 does NOT allow int main() - only void main() is valid
        // This corrects Johannes' feedback: "int main() { return 0; }" gives compilation error
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));
        String code = "int main() { return 0; }";
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertProblems(result);
    }

    @Test
    void testInvalidMainMethodWithExtraParameters() {
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));
        String code = "void main(String[] args, int x) { }";
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertTrue(result.getProblems().stream()
                .anyMatch(p -> p.getMessage().contains("Main method must have zero or one parameter")));
    }

    @Test
    void testMixedCompactAndRegularClasses() {
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));
        String code = "void main() { } class Helper { }";
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        assertTrue(cu.getTypes().size() >= 1);
        assertTrue(result.getProblems().isEmpty());
    }

    @Test
    void testCompactClassWithFields() {
        // Test compact classes can have fields
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));
        String code = "String greeting = \"Hello\"; void main() { }";
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
        assertTrue(result.isSuccessful());
    }

    @Test
    void testCompactClassValidationForOlderVersions() {
        JavaParser parser24 = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_24));
        String code = "class Test { void main() { } }";
        ParseResult<CompilationUnit> result = parser24.parse(code);
        assertProblems(result);
    }

    @Test
    void testRegularClassStillWorks() {
        // Regular class declarations should still work
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));
        String code = "class RegularClass { void main() { } }";
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
        assertTrue(result.isSuccessful());

        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration regularClass =
                cu.getClassByName("RegularClass").get();
        assertFalse(regularClass.getIsCompact());
    }
}
