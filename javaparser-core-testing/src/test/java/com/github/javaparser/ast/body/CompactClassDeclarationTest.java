/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import static com.github.javaparser.utils.TestParser.parseCompilationUnit;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.TypeParameter;
import org.junit.jupiter.api.Test;

/**
 * Tests for JEP 512: Unnamed Classes and Instance Main Methods (Compact Classes).
 * Introduced in Java 21 (preview) and finalized in Java 25.
 */
class CompactClassDeclarationTest {

    /**
     * Helper method to assert that a class declaration represents a compact (unnamed) class.
     * A compact class should:
     * - Be implicitly final
     * - Have no explicit name or be named according to the compilation unit
     * - Have the compact field set to true
     */
    private void assertIsCompactClass(ClassOrInterfaceDeclaration classDecl) {
        assertNotNull(classDecl);
        assertTrue(classDecl.isFinal(), "Compact class should be implicitly final");
        assertFalse(classDecl.isInterface(), "Compact class should not be an interface");
        assertTrue(classDecl.isCompact(), "Compact class should be marked as such");
    }

    @Test
    void minimalCompactClass() {
        String s = "void main() {\n" + "    System.out.println(\"Hello, World!\");\n" + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);

        assertEquals(1, cu.getTypes().size());
        TypeDeclaration<?> typeDecl = cu.getType(0);
        assertTrue(typeDecl.isClassOrInterfaceDeclaration());

        ClassOrInterfaceDeclaration classDecl = typeDecl.asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(1, members.size());

        assertTrue(members.get(0).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(0).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
        assertTrue(mainMethod.getType().isVoidType());
        assertFalse(mainMethod.isStatic(), "Instance main method should not be static");
        assertEquals(0, mainMethod.getParameters().size());
    }

    @Test
    void compactClassWithInstanceField() {
        String s = "int count = 0;\n" + "\n" + "void main() {\n" + "    count++;\n" + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isFieldDeclaration());
        FieldDeclaration field = members.get(0).asFieldDeclaration();
        assertEquals("count", field.getVariable(0).getNameAsString());
        assertTrue(field.getVariable(0).getType().isPrimitiveType());
        assertEquals(
                PrimitiveType.Primitive.INT,
                field.getVariable(0).getType().asPrimitiveType().getType());
        assertTrue(field.getVariable(0).getInitializer().isPresent());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithMultipleMethods() {
        String s = "int add(int a, int b) {\n" + "    return a + b;\n" + "}\n" + "\n" + "void main() {}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isMethodDeclaration());
        MethodDeclaration addMethod = members.get(0).asMethodDeclaration();
        assertEquals("add", addMethod.getNameAsString());
        assertTrue(addMethod.getType().isPrimitiveType());
        assertEquals(
                PrimitiveType.Primitive.INT,
                addMethod.getType().asPrimitiveType().getType());
        assertEquals(2, addMethod.getParameters().size());
        assertEquals("a", addMethod.getParameter(0).getNameAsString());
        assertEquals("b", addMethod.getParameter(1).getNameAsString());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
        assertTrue(mainMethod.getType().isVoidType());
    }

    @Test
    void compactClassWithStaticAndInstanceMembers() {
        String s = "static final String GREETING = \"Hello\";\n"
                + "String name = \"World\";\n"
                + "\n"
                + "static String formatMessage(String msg) {\n"
                + "    return msg.toUpperCase();\n"
                + "}\n"
                + "\n"
                + "void main() {}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(4, members.size());

        assertTrue(members.get(0).isFieldDeclaration());
        FieldDeclaration greetingField = members.get(0).asFieldDeclaration();
        assertEquals("GREETING", greetingField.getVariable(0).getNameAsString());
        assertTrue(greetingField.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(greetingField.hasModifier(Modifier.Keyword.FINAL));

        assertTrue(members.get(1).isFieldDeclaration());
        FieldDeclaration nameField = members.get(1).asFieldDeclaration();
        assertEquals("name", nameField.getVariable(0).getNameAsString());
        assertFalse(nameField.hasModifier(Modifier.Keyword.STATIC));

        assertTrue(members.get(2).isMethodDeclaration());
        MethodDeclaration formatMethod = members.get(2).asMethodDeclaration();
        assertEquals("formatMessage", formatMethod.getNameAsString());
        assertTrue(formatMethod.hasModifier(Modifier.Keyword.STATIC));

        assertTrue(members.get(3).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(3).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
        assertFalse(mainMethod.hasModifier(Modifier.Keyword.STATIC));
    }

    @Test
    void compactClassWithNestedClass() {
        String s = "class Inner {\n"
                + "    void greet() {\n"
                + "        System.out.println(\"Hello from Inner\");\n"
                + "    }\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    Inner inner = new Inner();\n"
                + "    inner.greet();\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isClassOrInterfaceDeclaration());
        ClassOrInterfaceDeclaration innerClass = members.get(0).asClassOrInterfaceDeclaration();
        assertEquals("Inner", innerClass.getNameAsString());
        assertEquals("$COMPACT_CLASS.Inner", innerClass.getFullyQualifiedName().get());
        assertEquals(1, innerClass.getMethods().size());
        assertEquals("greet", innerClass.getMethods().get(0).getNameAsString());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithArrayField() {
        String s = "int[] numbers = {1, 2, 3, 4, 5};\n" + "\n" + "void main() {\n" + "    printNumbers();\n" + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isFieldDeclaration());
        FieldDeclaration field = members.get(0).asFieldDeclaration();
        assertEquals("numbers", field.getVariable(0).getNameAsString());
        assertTrue(field.getVariable(0).getType().isArrayType());

        ArrayType arrayType = field.getVariable(0).getType().asArrayType();
        assertTrue(arrayType.getComponentType().isPrimitiveType());
        assertEquals(
                PrimitiveType.Primitive.INT,
                arrayType.getComponentType().asPrimitiveType().getType());
        assertTrue(field.getVariable(0).getInitializer().isPresent());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithGenericMethod() {
        String s = "<T> void printValue(T value) {\n"
                + "    System.out.println(\"Value: \" + value);\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    printValue(\"String\");\n"
                + "    printValue(42);\n"
                + "    printValue(3.14);\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isMethodDeclaration());
        MethodDeclaration printValueMethod = members.get(0).asMethodDeclaration();
        assertEquals("printValue", printValueMethod.getNameAsString());

        NodeList<TypeParameter> typeParameters = printValueMethod.getTypeParameters();
        assertEquals(1, typeParameters.size());
        assertEquals("T", typeParameters.get(0).getNameAsString());

        assertEquals(1, printValueMethod.getParameters().size());
        assertEquals("value", printValueMethod.getParameter(0).getNameAsString());
        assertTrue(printValueMethod.getParameter(0).getType().isClassOrInterfaceType());
        assertEquals(
                "T",
                printValueMethod
                        .getParameter(0)
                        .getType()
                        .asClassOrInterfaceType()
                        .getNameAsString());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithRecord() {
        String s = "record Person(String name, int age) {}\n"
                + "\n"
                + "void main() {\n"
                + "    Person p = new Person(\"Alice\", 30);\n"
                + "    System.out.println(p.name() + \" is \" + p.age() + \" years old\");\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isRecordDeclaration());
        RecordDeclaration recordDecl = members.get(0).asRecordDeclaration();
        assertEquals("Person", recordDecl.getNameAsString());
        assertEquals(2, recordDecl.getParameters().size());
        assertEquals("name", recordDecl.getParameters().get(0).getNameAsString());
        assertEquals("age", recordDecl.getParameters().get(1).getNameAsString());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithEnum() {
        String s = "enum Color {\n"
                + "    RED, GREEN, BLUE\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    for (Color c : Color.values()) {\n"
                + "        System.out.println(c);\n"
                + "    }\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isEnumDeclaration());
        EnumDeclaration enumDecl = members.get(0).asEnumDeclaration();
        assertEquals("Color", enumDecl.getNameAsString());
        assertEquals(3, enumDecl.getEntries().size());
        assertEquals("RED", enumDecl.getEntries().get(0).getNameAsString());
        assertEquals("GREEN", enumDecl.getEntries().get(1).getNameAsString());
        assertEquals("BLUE", enumDecl.getEntries().get(2).getNameAsString());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithInterface() {
        String s = "interface Printer {\n"
                + "    void print();\n"
                + "}\n"
                + "\n"
                + "class ConsolePrinter implements Printer {\n"
                + "    public void print() {\n"
                + "        System.out.println(\"Printing...\");\n"
                + "    }\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    Printer p = new ConsolePrinter();\n"
                + "    p.print();\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(3, members.size());

        assertTrue(members.get(0).isClassOrInterfaceDeclaration());
        ClassOrInterfaceDeclaration printerInterface = members.get(0).asClassOrInterfaceDeclaration();
        assertTrue(printerInterface.isInterface());
        assertEquals("Printer", printerInterface.getNameAsString());
        assertEquals(1, printerInterface.getMethods().size());

        assertTrue(members.get(1).isClassOrInterfaceDeclaration());
        ClassOrInterfaceDeclaration consolePrinterClass = members.get(1).asClassOrInterfaceDeclaration();
        assertFalse(consolePrinterClass.isInterface());
        assertEquals("ConsolePrinter", consolePrinterClass.getNameAsString());
        assertEquals(1, consolePrinterClass.getImplementedTypes().size());
        assertEquals("Printer", consolePrinterClass.getImplementedTypes().get(0).getNameAsString());

        assertTrue(members.get(2).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(2).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithVarargs() {
        String s = "int sum(int... numbers) {\n"
                + "    int total = 0;\n"
                + "    for (int n : numbers) {\n"
                + "        total += n;\n"
                + "    }\n"
                + "    return total;\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    System.out.println(sum(1, 2, 3, 4, 5));\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isMethodDeclaration());
        MethodDeclaration sumMethod = members.get(0).asMethodDeclaration();
        assertEquals("sum", sumMethod.getNameAsString());
        assertEquals(1, sumMethod.getParameters().size());

        Parameter varargsParam = sumMethod.getParameter(0);
        assertEquals("numbers", varargsParam.getNameAsString());
        assertTrue(varargsParam.isVarArgs(), "Parameter should be varargs");
        assertTrue(varargsParam.getType().isPrimitiveType());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithExceptionHandling() {
        String s = "void riskyOperation() throws Exception {\n"
                + "    throw new Exception(\"Something went wrong\");\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    try {\n"
                + "        riskyOperation();\n"
                + "    } catch (Exception e) {\n"
                + "        System.out.println(\"Caught: \" + e.getMessage());\n"
                + "    }\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isMethodDeclaration());
        MethodDeclaration riskyMethod = members.get(0).asMethodDeclaration();
        assertEquals("riskyOperation", riskyMethod.getNameAsString());
        assertEquals(1, riskyMethod.getThrownExceptions().size());

        ClassOrInterfaceType exceptionType =
                riskyMethod.getThrownExceptions().get(0).asClassOrInterfaceType();
        assertEquals("Exception", exceptionType.getNameAsString());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithAnnotationDeclaration() {
        String s = "@interface MyAnnotation {\n"
                + "    String value() default \"\";\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    System.out.println(\"Annotation declared\");\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isAnnotationDeclaration());
        AnnotationDeclaration annotationDecl = members.get(0).asAnnotationDeclaration();
        assertEquals("MyAnnotation", annotationDecl.getNameAsString());

        assertEquals(1, annotationDecl.getMembers().size());
        BodyDeclaration<?> annotationMember = annotationDecl.getMember(0);
        assertTrue(annotationMember.isAnnotationMemberDeclaration());

        AnnotationMemberDeclaration valueMember = annotationMember.asAnnotationMemberDeclaration();
        assertEquals("value", valueMember.getNameAsString());
        assertTrue(valueMember.getDefaultValue().isPresent());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(1).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithAnnotationDeclarationAfterMainMethod() {
        String s = "void main() {\n"
                + "    System.out.println(\"Annotation declared\");\n"
                + "}\n"
                + "@interface MyAnnotation {\n"
                + "    String value() default \"\";\n"
                + "}\n"
                + "\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(2, members.size());

        assertTrue(members.get(0).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(0).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());

        assertTrue(members.get(1).isAnnotationDeclaration());
        AnnotationDeclaration annotationDecl = members.get(1).asAnnotationDeclaration();
        assertEquals("MyAnnotation", annotationDecl.getNameAsString());

        assertEquals(1, annotationDecl.getMembers().size());
        BodyDeclaration<?> annotationMember = annotationDecl.getMember(0);
        assertTrue(annotationMember.isAnnotationMemberDeclaration());

        AnnotationMemberDeclaration valueMember = annotationMember.asAnnotationMemberDeclaration();
        assertEquals("value", valueMember.getNameAsString());
        assertTrue(valueMember.getDefaultValue().isPresent());
    }

    @Test
    void compactClassWithAnnotatedMethods() {
        String s = "@Deprecated\n"
                + "void oldMethod() {\n"
                + "    System.out.println(\"This is deprecated\");\n"
                + "}\n"
                + "\n"
                + "@Override\n"
                + "public String toString() {\n"
                + "    return \"AnnotatedMethod\";\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    oldMethod();\n"
                + "    System.out.println(toString());\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(3, members.size());

        assertTrue(members.get(0).isMethodDeclaration());
        MethodDeclaration oldMethod = members.get(0).asMethodDeclaration();
        assertEquals("oldMethod", oldMethod.getNameAsString());
        assertEquals(1, oldMethod.getAnnotations().size());

        AnnotationExpr deprecatedAnnotation = oldMethod.getAnnotations().get(0);
        assertEquals("Deprecated", deprecatedAnnotation.getNameAsString());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration toStringMethod = members.get(1).asMethodDeclaration();
        assertEquals("toString", toStringMethod.getNameAsString());
        assertEquals(1, toStringMethod.getAnnotations().size());

        AnnotationExpr overrideAnnotation = toStringMethod.getAnnotations().get(0);
        assertEquals("Override", overrideAnnotation.getNameAsString());

        assertTrue(members.get(2).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(2).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    void compactClassWithCustomAnnotationAndAnnotatedMethods() {
        String s = "@interface Author {\n"
                + "    String name();\n"
                + "}\n"
                + "\n"
                + "@Override\n"
                + "int calculate(int x) {\n"
                + "    return x * 2;\n"
                + "}\n"
                + "\n"
                + "void main() {}\n";

        CompilationUnit cu = parseCompilationUnit(s);
        ClassOrInterfaceDeclaration classDecl = cu.getType(0).asClassOrInterfaceDeclaration();

        assertIsCompactClass(classDecl);
        assertEquals("$COMPACT_CLASS", classDecl.getNameAsString());

        NodeList<BodyDeclaration<?>> members = classDecl.getMembers();
        assertEquals(3, members.size());

        assertTrue(members.get(0).isAnnotationDeclaration());
        AnnotationDeclaration authorAnnotation = members.get(0).asAnnotationDeclaration();
        assertEquals("Author", authorAnnotation.getNameAsString());
        assertEquals(1, authorAnnotation.getMembers().size());

        AnnotationMemberDeclaration nameMember = authorAnnotation.getMember(0).asAnnotationMemberDeclaration();
        assertEquals("name", nameMember.getNameAsString());

        assertTrue(members.get(1).isMethodDeclaration());
        MethodDeclaration calculateMethod = members.get(1).asMethodDeclaration();
        assertEquals("calculate", calculateMethod.getNameAsString());
        assertEquals(1, calculateMethod.getAnnotations().size());

        AnnotationExpr overrideAnnotation = calculateMethod.getAnnotations().get(0);
        assertEquals("Override", overrideAnnotation.getNameAsString());
        assertTrue(overrideAnnotation.isMarkerAnnotationExpr());

        assertTrue(members.get(2).isMethodDeclaration());
        MethodDeclaration mainMethod = members.get(2).asMethodDeclaration();
        assertEquals("main", mainMethod.getNameAsString());
    }

    @Test
    public void commentInCompactClassMethodBody() {
        String code = "void foo() {\n" + "    // Some comment\n" + "    int x;\n" + "}";

        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
    }

    @Test
    public void trailingCommentInCompactClass() {
        String code = "void foo() {\n" + "}\n" + "// Some comment";

        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
    }
}
