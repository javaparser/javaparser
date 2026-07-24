/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

class MethodReferenceResolutionTest extends AbstractResolutionTest {

    @Test
    void classMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "classMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.Object.hashCode()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void superclassMethodNotOverridden() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "superclassMethodNotOverridden");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.Object.hashCode()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void superclassMethodOverridden() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "superclassMethodOverridden");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.String.hashCode()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void superclassMethodWithSubclassType() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "superclassMethodWithSubclassType");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.Object.hashCode()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void fieldAccessMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "fieldAccessMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals(
                "java.io.PrintStream.println(java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void thisClassMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "thisClassMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("MethodReferences.print(java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void superclassMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "superclassMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.print(java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void instanceMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "instanceMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.util.List.add(E)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void staticMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "staticMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.print(java.lang.Boolean)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void biFunction() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "biFunction");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals(
                "SuperClass.isEqualAsStrings(java.lang.Integer, java.lang.String)",
                resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void customTriFunction() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "customTriFunction");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals(
                "SuperClass.getOneNumberAsString(java.lang.Integer, java.lang.Integer, java.lang.Integer)",
                resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void consumerDeclaredInMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "consumerDeclaredInMethod");
        MethodReferenceExpr methodReferenceExpr =
                method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("MethodReferences.print(java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void functionDeclaredInMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "functionDeclaredInMethod");
        MethodReferenceExpr methodReferenceExpr =
                method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.returnSameValue(java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void biFunctionDeclaredInMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "biFunctionDeclaredInMethod");
        MethodReferenceExpr methodReferenceExpr =
                method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals(
                "SuperClass.isEqual(java.lang.Integer, java.lang.Integer)",
                resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void consumerUsedInStream() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "consumerUsedInStream");
        MethodReferenceExpr methodReferenceExpr =
                method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.print(java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void functionUsedInStream() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "functionUsedInStream");
        MethodReferenceExpr methodReferenceExpr =
                method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals(
                "SuperClass.returnSameValue(java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void biFunctionUsedInStream() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "biFunctionUsedInStream");
        MethodReferenceExpr methodReferenceExpr =
                method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals(
                "SuperClass.add(java.lang.Integer, java.lang.Integer)",
                resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void biFunctionInMethodCall() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "biFunctionInMethodCall");
        MethodReferenceExpr methodReferenceExpr =
                method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals(
                "SuperClass.isEqualAsStrings(java.lang.Integer, java.lang.String)",
                resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    public void resolveOverloadedMethodReference() {
        String s = "import java.util.HashSet;\n" + "import java.util.Set;\n"
                + "import java.util.stream.Collectors;\n"
                + "\n"
                + "public class StreamTest {\n"
                + "    \n"
                + "    public void streamTest () {\n"
                + "        Set<Integer> intSet = new HashSet<Integer>() {{\n"
                + "           add(1);\n"
                + "           add(2);\n"
                + "        }};\n"
                + "        Set <String> strings = intSet.stream().map(String::valueOf).collect(Collectors.toSet());\n"
                + "    }\n"
                + "}";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(s);

        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "StreamTest");
        MethodDeclaration method = Navigator.demandMethod(clazz, "streamTest");
        MethodReferenceExpr methodReferenceExpr =
                method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.String.valueOf(java.lang.Object)", resolvedMethodDeclaration.getQualifiedSignature());

        // resolve parent method call (cfr issue #2657)
        MethodCallExpr methodCallExpr =
                (MethodCallExpr) methodReferenceExpr.getParentNode().get();
        ResolvedMethodDeclaration callMethodDeclaration = methodCallExpr.resolve();
        assertEquals(
                "java.util.stream.Stream.map(java.util.function.Function<? super T, ? extends R>)",
                callMethodDeclaration.getQualifiedSignature());
    }

    @Test
    public void issue2657Test_StringValueOfInStream() {
        String s = "import java.util.HashSet;\n" + "import java.util.Set;\n"
                + "import java.util.stream.Collectors;\n"
                + "\n"
                + "public class StreamTest {\n"
                + "    \n"
                + "    public void streamTest () {\n"
                + "        Set<Integer> intSet = new HashSet<Integer>() {{\n"
                + "           add(1);\n"
                + "           add(2);\n"
                + "        }};\n"
                + "        Set <String> strings = intSet.stream().map(String::valueOf).collect(Collectors.toSet());\n"
                + "    }\n"
                + "}";

        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(s);

        int errorCount = 0;

        Set<MethodCallExpr> methodCallExpr = new HashSet<>(cu.findAll(MethodCallExpr.class));
        for (MethodCallExpr expr : methodCallExpr) {
            try {
                ResolvedMethodDeclaration rd = expr.resolve();
            } catch (UnsolvedSymbolException e) {
                errorCount++;
            }
        }

        assertEquals(0, errorCount, "Expected zero UnsolvedSymbolException s");
    }

    @Test
    public void instanceMethodReferenceTest() {
        // Cfr. #2666
        String s = "import java.util.stream.Stream;\n" + "import java.util.List;\n"
                + "\n"
                + "public class StreamTest {\n"
                + "\n"
                + "    public void streamTest() {\n"
                + "        String[] arr = {\"1\", \"2\", \"3\", \"\", null};\n"
                + "List<String> list = null;\n"
                + "        list.stream().filter(this::isNotEmpty).forEach(s -> System.out.println(s));\n"
                + "    }\n"
                + "\n"
                + "    private boolean isNotEmpty(String s) {\n"
                + "        return s != null && s.length() > 0;\n"
                + "    }\n"
                + "}\n";
        TypeSolver typeSolver = new ReflectionTypeSolver(false);
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(s);
        Set<MethodCallExpr> methodCallExpr = new HashSet<>(cu.findAll(MethodCallExpr.class));

        int errorCount = 0;

        for (MethodCallExpr expr : methodCallExpr) {
            ResolvedMethodDeclaration rd = expr.resolve();
        }

        assertEquals(0, errorCount, "Expected zero UnsolvedSymbolException s");
    }

    @Test
    public void unboundNonStaticMethodsTest() {
        // Example from:
        // https://javaworld.com/article/2946534/java-101-the-essential-java-language-features-tour-part-7.html
        String s = "import java.util.function.Function;\n" + "\n"
                + "public class MRDemo\n"
                + "{\n"
                + "   public static void main(String[] args)\n"
                + "   {\n"
                + "      print(String::toLowerCase, \"STRING TO LOWERCASE\");\n"
                + "      print(s -> s.toLowerCase(), \"STRING TO LOWERCASE\");\n"
                + "      print(new Function<String, String>()\n"
                + "      {\n"
                + "         @Override\n"
                + "         public String apply(String s) // receives argument in parameter s;\n"
                + "         {                             // doesn't need to close over s\n"
                + "            return s.toLowerCase();\n"
                + "         }\n"
                + "      }, \"STRING TO LOWERCASE\");\n"
                + "   }\n"
                + "\n"
                + "   public static void print(Function<String, String> function, String\n"
                + "s)\n"
                + "   {\n"
                + "      System.out.println(function.apply(s));\n"
                + "   }\n"
                + "}";

        TypeSolver typeSolver = new ReflectionTypeSolver(false);
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(s);
        Set<MethodCallExpr> methodCallExpr = new HashSet<>(cu.findAll(MethodCallExpr.class));

        int errorCount = 0;

        for (MethodCallExpr expr : methodCallExpr) {
            ResolvedMethodDeclaration rd = expr.resolve();
        }

        assertEquals(0, errorCount, "Expected zero UnsolvedSymbolException s");
    }

    /**
     * BinaryOperator inherits its functional method apply(T, U) from BiFunction, so resolving
     * BigDecimal::add must bind the ancestor's type parameters instead of leaking them unresolved.
     * See <a href="https://github.com/javaparser/javaparser/issues/4936">issue #4936</a>.
     */
    @Test
    public void issue4936_inheritedFunctionalMethodTypeParametersDoNotLeak() {
        String code = "import java.math.BigDecimal;\n" + "import java.util.stream.Stream;\n"
                + "public class Test{\n"
                + "    public void test(){\n"
                + "        Stream.of(new BigDecimal(0L)).reduce(BigDecimal::add).orElse(null);\n"
                + "    }\n"
                + "}";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(code);

        assertEquals(
                "java.util.stream.Stream.of(T)",
                Navigator.findMethodCall(cu, "of").get().resolve().getQualifiedSignature());
        assertEquals(
                "java.util.stream.Stream.reduce(java.util.function.BinaryOperator<T>)",
                Navigator.findMethodCall(cu, "reduce").get().resolve().getQualifiedSignature());
        assertEquals(
                "java.util.Optional.orElse(T)",
                Navigator.findMethodCall(cu, "orElse").get().resolve().getQualifiedSignature());
    }

    /**
     * Inherited functional method type parameters must not leak even when the interface declares
     * no type parameters of its own, leaving name-based matching nothing to bind.
     * See <a href="https://github.com/javaparser/javaparser/issues/4936">issue #4936</a>.
     */
    @Test
    public void issue4936_inheritedFunctionalMethodTypeParametersDoNotLeak_noOwnTypeParameters() {
        String code = "import java.math.BigDecimal;\n"
                + "public class Test {\n"
                + "    interface DecimalOp extends java.util.function.BinaryOperator<BigDecimal> {}\n"
                + "    static BigDecimal use(DecimalOp op) { return null; }\n"
                + "    public void test() {\n"
                + "        use(BigDecimal::add).negate();\n"
                + "    }\n"
                + "}";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(code);

        assertEquals(
                "Test.use(Test.DecimalOp)",
                Navigator.findMethodCall(cu, "use").get().resolve().getQualifiedSignature());
        assertEquals(
                "java.math.BigDecimal.negate()",
                Navigator.findMethodCall(cu, "negate").get().resolve().getQualifiedSignature());
    }

    /**
     * Inherited functional method type parameters must not leak across a multi-level inheritance
     * chain whose own type-parameter names differ from the ancestor's.
     * See <a href="https://github.com/javaparser/javaparser/issues/4936">issue #4936</a>.
     */
    @Test
    public void issue4936_inheritedFunctionalMethodTypeParametersDoNotLeak_transitiveInheritance() {
        String code = "import java.math.BigDecimal;\n"
                + "public class Test {\n"
                + "    interface Step1<Z> extends java.util.function.BiFunction<Z, Z, Z> {}\n"
                + "    interface Step2<A> extends Step1<A> {}\n"
                + "    static BigDecimal use(Step2<BigDecimal> op) { return null; }\n"
                + "    public void test() {\n"
                + "        use(BigDecimal::add).negate();\n"
                + "    }\n"
                + "}";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(code);

        assertEquals(
                "Test.use(Test.Step2<java.math.BigDecimal>)",
                Navigator.findMethodCall(cu, "use").get().resolve().getQualifiedSignature());
        assertEquals(
                "java.math.BigDecimal.negate()",
                Navigator.findMethodCall(cu, "negate").get().resolve().getQualifiedSignature());
    }

    /**
     * Inherited functional method type parameters must not leak when resolving a static method
     * reference (JLS §15.13.1 form 1a), not just an unbound instance one.
     * See <a href="https://github.com/javaparser/javaparser/issues/4936">issue #4936</a>.
     */
    @Test
    public void issue4936_inheritedFunctionalMethodTypeParametersDoNotLeak_staticMethodReference() {
        String code = "import java.util.stream.Stream;\n"
                + "public class Test {\n"
                + "    public void test() {\n"
                + "        Stream.of(1).reduce(Integer::sum).orElse(null);\n"
                + "    }\n"
                + "}";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(code);

        assertEquals(
                "java.util.stream.Stream.of(T)",
                Navigator.findMethodCall(cu, "of").get().resolve().getQualifiedSignature());
        assertEquals(
                "java.util.stream.Stream.reduce(java.util.function.BinaryOperator<T>)",
                Navigator.findMethodCall(cu, "reduce").get().resolve().getQualifiedSignature());
        assertEquals(
                "java.util.Optional.orElse(T)",
                Navigator.findMethodCall(cu, "orElse").get().resolve().getQualifiedSignature());
    }

    /**
     * Inherited functional method type parameters bound to a wildcard type argument must be
     * substituted (and then unwrapped) instead of leaking.
     * See <a href="https://github.com/javaparser/javaparser/issues/4936">issue #4936</a>.
     */
    @Test
    public void issue4936_inheritedFunctionalMethodTypeParametersDoNotLeak_wildcardTypeArgument() {
        String code = "import java.math.BigDecimal;\n"
                + "public class Test {\n"
                + "    interface Op<A> extends java.util.function.BiFunction<A, A, A> {}\n"
                + "    static BigDecimal use(Op<? super BigDecimal> op) { return null; }\n"
                + "    public void test() {\n"
                + "        use(BigDecimal::add).negate();\n"
                + "    }\n"
                + "}";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(code);

        assertEquals(
                "Test.use(Test.Op<? super java.math.BigDecimal>)",
                Navigator.findMethodCall(cu, "use").get().resolve().getQualifiedSignature());
        assertEquals(
                "java.math.BigDecimal.negate()",
                Navigator.findMethodCall(cu, "negate").get().resolve().getQualifiedSignature());
    }

    /**
     * Without a chained call, resolving reduce() does not force full type resolution of the
     * method reference argument; this is the case that already worked before issue #4936.
     * See <a href="https://github.com/javaparser/javaparser/issues/4936">issue #4936</a>.
     */
    @Test
    public void issue4936_inheritedFunctionalMethodTypeParametersDoNotLeak_withoutChainedCall() {
        String code = "import java.math.BigDecimal;\n" + "import java.util.stream.Stream;\n"
                + "public class Test{\n"
                + "    public void test(){\n"
                + "        Stream.of(new BigDecimal(0L)).reduce(BigDecimal::add);\n"
                + "    }\n"
                + "}";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(code);

        assertEquals(
                "java.util.stream.Stream.of(T)",
                Navigator.findMethodCall(cu, "of").get().resolve().getQualifiedSignature());
        assertEquals(
                "java.util.stream.Stream.reduce(java.util.function.BinaryOperator<T>)",
                Navigator.findMethodCall(cu, "reduce").get().resolve().getQualifiedSignature());
    }

    @Test
    public void testIssue3289() {
        String code = "import java.util.ArrayList;\n" + "import java.util.List;\n"
                + "\n"
                + "public class testHLS2 {\n"
                + "\n"
                + "    static class C {\n"
                + "        void print(String s) { }\n"
                + "    }\n"
                + "\n"
                + "    public static void main(String[] args) {\n"
                + "        C c = new C();\n"
                + "        List<String> l = new ArrayList<>();\n"
                + "        l.forEach(c::print);\n"
                + "    }\n"
                + "}\n";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(code);

        int errorCount = 0;

        Set<MethodReferenceExpr> methodeRefExpr = new HashSet<>(cu.findAll(MethodReferenceExpr.class));
        for (MethodReferenceExpr expr : methodeRefExpr) {
            try {
                ResolvedMethodDeclaration md = expr.resolve();
            } catch (UnsolvedSymbolException e) {
                errorCount++;
            }
        }

        assertEquals(0, errorCount, "Expected zero UnsolvedSymbolException s");
    }

    @Test
    @Disabled(value = "Waiting for constructor calls to be resolvable")
    void zeroArgumentConstructor_resolveToDeclaration() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "zeroArgumentConstructor");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("Supplier<SuperClass>", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void zeroArgumentConstructor() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "zeroArgumentConstructor");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        ResolvedType resolvedType = methodReferenceExpr.calculateResolvedType();

        // Per JLS §15.13 a constructor reference is a poly expression whose type is the
        // functional interface declared by the enclosing context (here: the method return type
        // Supplier<SuperClass>), not the constructed type (SuperClass).
        assertEquals("Supplier<SuperClass>", resolvedType.describe());
    }

    @Test
    void singleArgumentConstructor() {
        // configure symbol solver before parsing
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz =
                Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "singleArgumentConstructor");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr =
                (MethodReferenceExpr) returnStmt.getExpression().get();

        ResolvedType resolvedType = methodReferenceExpr.calculateResolvedType();

        // Per JLS §15.13 a constructor reference is a poly expression whose type is the
        // functional interface declared by the enclosing context (here: the method return type
        // Function<String, SuperClass>), not the constructed type (SuperClass).
        assertEquals("Function<java.lang.String, SuperClass>", resolvedType.describe());
    }
}
