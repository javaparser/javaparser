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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;

public class JavaParserRecordDeclarationTest {

    private final String basicRecord = "record Test() {}";
    private final String basicRecordWithPackage = "package x.y; record Test() {}";
    private final String basicRecordWithImplements = "" + "interface A {}\n" + "record Test() implements A {}";

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        // clear internal caches
        JavaParserFacade.clearInstances();

        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()))
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16);

        javaParser = new JavaParser(configuration);
    }

    @Test
    void testIsRecord() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertTrue(resolvedReferenceTypeDeclaration.isRecord());
    }

    @Test
    void testIsClass() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertFalse(resolvedReferenceTypeDeclaration.isClass());
    }

    @Test
    void testIsInterface() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertFalse(resolvedReferenceTypeDeclaration.isInterface());
    }

    @Test
    void testIsEnum() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertFalse(resolvedReferenceTypeDeclaration.isEnum());
    }

    @Test
    void testIsTypeVariable() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertFalse(resolvedReferenceTypeDeclaration.isTypeParameter());
    }

    @Test
    void testIsType() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertTrue(resolvedReferenceTypeDeclaration.isType());
    }

    @Test
    void testAsType() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals(resolvedReferenceTypeDeclaration, resolvedReferenceTypeDeclaration.asType());
    }

    @Test
    void testAsClass() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
            CompilationUnit compilationUnit = x.getResult().get();

            RecordDeclaration recordDeclaration =
                    compilationUnit.findFirst(RecordDeclaration.class).get();
            ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

            assertEquals(resolvedReferenceTypeDeclaration, resolvedReferenceTypeDeclaration.asClass());
        });
    }

    @Test
    void testAsRecord() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals(resolvedReferenceTypeDeclaration, resolvedReferenceTypeDeclaration.asRecord());
    }

    @Test
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
            CompilationUnit compilationUnit = x.getResult().get();

            RecordDeclaration recordDeclaration =
                    compilationUnit.findFirst(RecordDeclaration.class).get();
            ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

            resolvedReferenceTypeDeclaration.asInterface();
        });
    }

    @Test
    void testAsEnum() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
            CompilationUnit compilationUnit = x.getResult().get();

            RecordDeclaration recordDeclaration =
                    compilationUnit.findFirst(RecordDeclaration.class).get();
            ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

            resolvedReferenceTypeDeclaration.asEnum();
        });
    }

    @Test
    void testGetPackageName() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals("x.y", resolvedReferenceTypeDeclaration.getPackageName());
    }

    @Test
    void testGetClassName() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals("Test", resolvedReferenceTypeDeclaration.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithPackage);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        assertEquals("x.y.Test", resolvedReferenceTypeDeclaration.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

    @Test
    @EnabledForJreRange(max = org.junit.jupiter.api.condition.JRE.JAVA_13)
    void getGetAncestors_javaLangRecord_notAvailable() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithImplements);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        /*
         * `java.lang.Record` will have been introduced from  JRE14 preview / JRE16 release
         *  -- thus the `java.lang.Record` ancestor will not be available via classloader/reflection before these versions
         */
        assertThrows(UnsolvedSymbolException.class, () -> resolvedReferenceTypeDeclaration.getAncestors());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void getGetAncestors_javaLangRecord_available() {
        ParseResult<CompilationUnit> x = javaParser.parse(basicRecordWithImplements);
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = recordDeclaration.resolve();

        List<ResolvedReferenceType> ancestors = resolvedReferenceTypeDeclaration.getAncestors();
        assertEquals(2, ancestors.size());
        assertEquals("java.lang.Record", ancestors.get(0).getQualifiedName());
        assertEquals("A", ancestors.get(1).getQualifiedName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetDeclaredFields() {
        ParseResult<CompilationUnit> x = javaParser.parse("record Test(String s, Integer i) {}");
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        ResolvedReferenceTypeDeclaration resolvedDeclaration = recordDeclaration.resolve();

        List<ResolvedFieldDeclaration> fields = resolvedDeclaration.getAllFields();
        assertEquals(2, fields.size());
        assertEquals("java.lang.String", fields.get(0).getType().describe());
        assertEquals("s", fields.get(0).getName());
        assertEquals("java.lang.Integer", fields.get(1).getType().describe());
        assertEquals("i", fields.get(1).getName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetDeclaredMethods() {
        ParseResult<CompilationUnit> x = javaParser.parse("record Test(String s, Integer i) {\n"
                + "    public int foo(int x) {\n"
                + "        return x + i;\n"
                + "    }\n"
                + "}");
        CompilationUnit compilationUnit = x.getResult().get();

        RecordDeclaration recordDeclaration =
                compilationUnit.findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        Set<ResolvedMethodDeclaration> methods = resolvedRecordDeclaration.getDeclaredMethods();

        List<ResolvedMethodDeclaration> sortedMethods = methods.stream()
                .sorted(Comparator.comparing(ResolvedDeclaration::getName))
                .collect(Collectors.toList());

        assertEquals(3, sortedMethods.size());

        ResolvedMethodDeclaration fooMethod = sortedMethods.get(0);
        assertEquals("Test.foo", fooMethod.getQualifiedName());
        assertEquals("Test.foo(int)", fooMethod.getQualifiedSignature());
        assertEquals("int", fooMethod.getReturnType().describe());

        ResolvedMethodDeclaration implicitIMethod = sortedMethods.get(1);
        assertEquals("i", implicitIMethod.getName());
        assertEquals("Test.i", implicitIMethod.getQualifiedName());

        ResolvedMethodDeclaration implicitSMethod = sortedMethods.get(2);
        assertEquals("s", implicitSMethod.getName());
        assertEquals("Test.s", implicitSMethod.getQualifiedName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetSuperclass() {
        ParseResult<CompilationUnit> cu = javaParser.parse("record Foo(String s) {}");

        RecordDeclaration recordDeclaration =
                cu.getResult().get().findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        ResolvedReferenceType superClass =
                resolvedRecordDeclaration.getSuperClass().get();
        assertEquals("java.lang.Record", superClass.getQualifiedName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testImplicitGetterResolution() {
        ParseResult<CompilationUnit> cu = javaParser.parse("package test;\n"
                + "record Test(String s) {\n"
                + "    public String foo() {\n"
                + "        return s();\n"
                + "    }\n"
                + "}");

        MethodCallExpr sCall =
                Navigator.findMethodCall(cu.getResult().get(), "s").get();

        ResolvedMethodDeclaration resolvedCall = sCall.resolve();
        assertEquals("s", resolvedCall.getName());
        assertEquals("test.Test.s", resolvedCall.getQualifiedName());
        assertEquals("java.lang.String", resolvedCall.getReturnType().describe());
        assertEquals("test", resolvedCall.getPackageName());
        assertEquals("Test", resolvedCall.getClassName());
        assertEquals(0, resolvedCall.getNumberOfParams());
        assertEquals(0, resolvedCall.getNumberOfSpecifiedExceptions());
        assertEquals(AccessSpecifier.PUBLIC, resolvedCall.accessSpecifier());
        assertEquals("()Ljava/lang/String;", resolvedCall.toDescriptor());
        assertEquals("test.Test", resolvedCall.declaringType().getQualifiedName());

        assertFalse(resolvedCall.isAbstract());
        assertFalse(resolvedCall.isDefaultMethod());
        assertFalse(resolvedCall.isStatic());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testImplicitGetterSolvingFromDecl() {
        ParseResult<CompilationUnit> cu = javaParser.parse("package test;\n" + "record Test(String s) { }");

        RecordDeclaration recordDeclaration =
                cu.getResult().get().findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        SymbolReference<ResolvedMethodDeclaration> symbol =
                resolvedRecordDeclaration.solveMethod("s", Collections.emptyList());
        assertTrue(symbol.isSolved());
        ResolvedMethodDeclaration resolvedCall = symbol.getCorrespondingDeclaration();

        assertEquals("s", resolvedCall.getName());
        assertEquals("test.Test.s", resolvedCall.getQualifiedName());
        assertEquals("java.lang.String", resolvedCall.getReturnType().describe());
        assertEquals("test", resolvedCall.getPackageName());
        assertEquals("Test", resolvedCall.getClassName());
        assertEquals(0, resolvedCall.getNumberOfParams());
        assertEquals(0, resolvedCall.getNumberOfSpecifiedExceptions());
        assertEquals(AccessSpecifier.PUBLIC, resolvedCall.accessSpecifier());
        assertEquals("()Ljava/lang/String;", resolvedCall.toDescriptor());
        assertEquals("test.Test", resolvedCall.declaringType().getQualifiedName());

        assertFalse(resolvedCall.isAbstract());
        assertFalse(resolvedCall.isDefaultMethod());
        assertFalse(resolvedCall.isStatic());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testImplicitConstructor() {
        ParseResult<CompilationUnit> cu = javaParser.parse("package test;\nrecord Test(String s) { }");

        RecordDeclaration recordDeclaration =
                cu.getResult().get().findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        assertEquals(1, resolvedRecordDeclaration.getConstructors().size());

        ResolvedConstructorDeclaration constructor =
                resolvedRecordDeclaration.getConstructors().get(0);

        assertEquals("Test", constructor.getName());
        assertEquals("test.Test.Test", constructor.getQualifiedName());
        assertEquals(1, constructor.getNumberOfParams());
        assertEquals("test", constructor.getPackageName());
        assertEquals("Test", constructor.getClassName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testNonCanonicalConstructor() {
        ParseResult<CompilationUnit> cu = javaParser.parse("package test;\n"
                + "record Test(String s) {\n"
                + "    public Test(Object o) { s = o.toString(); }\n"
                + "}");

        RecordDeclaration recordDeclaration =
                cu.getResult().get().findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        assertEquals(2, resolvedRecordDeclaration.getConstructors().size());

        List<ResolvedConstructorDeclaration> sortedConstructors = resolvedRecordDeclaration.getConstructors().stream()
                .sorted(Comparator.comparing(
                        constructor -> constructor.getParam(0).describeType()))
                .collect(Collectors.toList());

        ResolvedConstructorDeclaration explicitConstructor = sortedConstructors.get(0);

        assertEquals("Test", explicitConstructor.getName());
        assertEquals("test.Test.Test", explicitConstructor.getQualifiedName());
        assertEquals(1, explicitConstructor.getNumberOfParams());
        assertEquals("test", explicitConstructor.getPackageName());
        assertEquals("Test", explicitConstructor.getClassName());
        assertEquals("java.lang.Object", explicitConstructor.getParam(0).describeType());

        ResolvedConstructorDeclaration implicitConstructor = sortedConstructors.get(1);

        assertEquals("Test", implicitConstructor.getName());
        assertEquals("test.Test.Test", implicitConstructor.getQualifiedName());
        assertEquals(1, implicitConstructor.getNumberOfParams());
        assertEquals("test", implicitConstructor.getPackageName());
        assertEquals("Test", implicitConstructor.getClassName());
        assertEquals("java.lang.String", implicitConstructor.getParam(0).describeType());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testInheritedMethods() {
        ParseResult<CompilationUnit> cu = javaParser.parse("package test;\n" + "interface Foo {\n"
                + "    default void foo() {}\n"
                + "}\n"
                + "record Test(String s)  implements Foo {}");

        RecordDeclaration recordDeclaration =
                cu.getResult().get().findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        ResolvedMethodDeclaration fooMethod = resolvedRecordDeclaration.getAllMethods().stream()
                .filter(methodUsage -> methodUsage.getName().equals("foo"))
                .findFirst()
                .get()
                .getDeclaration();
        assertEquals("test.Foo.foo", fooMethod.getQualifiedName());
        assertEquals("test.Foo.foo()", fooMethod.getQualifiedSignature());
        assertEquals("void", fooMethod.getReturnType().describe());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetAllStaticFields() {
        ParseResult<CompilationUnit> cu = javaParser.parse(
                "package test;\n" + "record Test(String s) {\n" + "    static Integer value = 2;" + "}");

        RecordDeclaration recordDeclaration =
                cu.getResult().get().findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        assertEquals(1, resolvedRecordDeclaration.getAllStaticFields().size());

        ResolvedFieldDeclaration staticField =
                resolvedRecordDeclaration.getAllStaticFields().get(0);

        assertEquals("value", staticField.getName());
        assertEquals("java.lang.Integer", staticField.getType().describe());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetAllNonStaticFields() {
        ParseResult<CompilationUnit> cu = javaParser.parse(
                "package test;\n" + "record Test(String s) {\n" + "    static Integer value = 2;" + "}");

        RecordDeclaration recordDeclaration =
                cu.getResult().get().findFirst(RecordDeclaration.class).get();
        JavaParserRecordDeclaration resolvedRecordDeclaration =
                (JavaParserRecordDeclaration) recordDeclaration.resolve();

        assertEquals(1, resolvedRecordDeclaration.getAllNonStaticFields().size());

        ResolvedFieldDeclaration field =
                resolvedRecordDeclaration.getAllNonStaticFields().get(0);

        assertEquals("s", field.getName());
        assertEquals("java.lang.String", field.getType().describe());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    public void testStaticMethod() {
        ParserConfiguration.LanguageLevel oldLevel =
                StaticJavaParser.getParserConfiguration().getLanguageLevel();
        StaticJavaParser.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16);
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit compilationUnit =
                StaticJavaParser.parse("public interface IUtil {\n" + "    record WrapperRecord(String name){}\n"
                        + "}\n"
                        + "\n"
                        + "public class Util implements IUtil {\n"
                        + "    public static Util create(String key) {\n"
                        + "        return new Util();\n"
                        + "    }\n"
                        + "}\n"
                        + "                \n"
                        + "public class Test {\n"
                        + "                \n"
                        + "    public void test() {\n"
                        + "        Util.create(\"foo\");\n"
                        + "    }\n"
                        + "                \n"
                        + "}\n");
        StaticJavaParser.getParserConfiguration().setLanguageLevel(oldLevel);

        for (MethodDeclaration method : compilationUnit.findAll(MethodDeclaration.class)) {
            for (MethodCallExpr call : method.findAll(MethodCallExpr.class)) {
                assertEquals("create", call.getNameAsString());
                assertEquals("Util.create(java.lang.String)", call.resolve().getQualifiedSignature());
            }
        }
    }

    void testGenericInvocation() {
        ParseResult<CompilationUnit> cu = javaParser.parse("record GenericBox<T> (T value) {}\n" + "class Test {\n"
                + "  public static void main(String[] args) {\n"
                + "    GenericBox<Integer> box = new GenericBox<>(2);\n"
                + "    System.out.println(box.value());\n"
                + "  }\n"
                + "}");

        MethodCallExpr valueCall = cu.getResult().get().findAll(MethodCallExpr.class).stream()
                .filter(call -> call.getNameAsString().equals("value"))
                .findFirst()
                .get();

        assertEquals("java.lang.Integer", valueCall.calculateResolvedType().describe());

        ResolvedMethodDeclaration resolvedValue = valueCall.resolve();
        assertEquals("T", resolvedValue.getReturnType().describe());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void genericConstructorTest() {
        ParseResult<CompilationUnit> cu = javaParser.parse("record GenericBox<T>(T value) {}\n"
                + "class Test {\n"
                + "  public static void main(String[] args) {\n"
                + "    GenericBox<Integer> box = new GenericBox<>(2);\n"
                + "    System.out.println(box.value());\n"
                + "  }\n"
                + "}");

        ObjectCreationExpr constructorInvocation =
                cu.getResult().get().findFirst(ObjectCreationExpr.class).get();

        assertEquals("GenericBox", constructorInvocation.getType().getNameAsString());
        assertEquals("GenericBox", constructorInvocation.getType().resolve().describe());
        assertEquals("GenericBox", constructorInvocation.calculateResolvedType().describe());
    }
}
