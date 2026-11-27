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

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Issue #4108: resolving method calls on annotation-typed receivers (both declared annotation elements
 * and methods inherited from {@code java.lang.annotation.Annotation} and {@code java.lang.Object}).
 */
class Issue4108Test {

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        JavaParserFacade.clearInstances();
        CombinedTypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver());
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17)
                .setSymbolResolver(new JavaSymbolSolver(typeSolver));
        javaParser = new JavaParser(configuration);
    }

    private CompilationUnit parse(String code) {
        return javaParser.parse(code).getResult().get();
    }

    @Test
    void resolveAnnotationMemberCallOnAnnotationVariable() {
        String code = "package hello;\n"
                + "@interface HasRoles {\n"
                + "    boolean skipCheck() default false;\n"
                + "}\n"
                + "class Main {\n"
                + "    void m() {\n"
                + "        HasRoles hasRoles = null;\n"
                + "        if (hasRoles != null) {\n"
                + "            if (hasRoles.skipCheck()) {}\n"
                + "        }\n"
                + "    }\n"
                + "}";

        CompilationUnit cu = parse(code);
        MethodCallExpr call = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("skipCheck"))
                .get();

        ResolvedMethodDeclaration resolved = call.resolve();
        assertEquals("hello.HasRoles.skipCheck()", resolved.getQualifiedSignature());
        assertEquals("boolean", resolved.getReturnType().describe());
        assertEquals(AccessSpecifier.PUBLIC, resolved.accessSpecifier());
        assertTrue(resolved.isAbstract());
        assertFalse(resolved.isStatic());
        assertFalse(resolved.isDefaultMethod());
        assertEquals(0, resolved.getNumberOfParams());
        assertEquals("()Z", resolved.toDescriptor());
        assertEquals("boolean", call.calculateResolvedType().describe());
    }

    @Test
    void resolveAnnotationMemberCallOnGetAnnotationResult() {
        String code = "package hello;\n"
                + "import java.lang.reflect.Field;\n"
                + "import java.util.HashMap;\n"
                + "import java.util.Map;\n"
                + "@interface DbFiled {\n"
                + "    String value();\n"
                + "}\n"
                + "class Request {\n"
                + "    private Class<?> clazz;\n"
                + "    private Map<String, Field> fieldMap = new HashMap<>();\n"
                + "    private void fieldMapInit() {\n"
                + "        Field[] fields = clazz.getDeclaredFields();\n"
                + "        for (Field field : fields) {\n"
                + "            if (field.isAnnotationPresent(DbFiled.class)) {\n"
                + "                fieldMap.put(field.getAnnotation(DbFiled.class).value(), field);\n"
                + "            }\n"
                + "        }\n"
                + "    }\n"
                + "}";

        CompilationUnit cu = parse(code);
        MethodCallExpr valueCall = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("value"))
                .get();

        assertEquals("hello.DbFiled.value()", valueCall.resolve().getQualifiedSignature());
        assertEquals("java.lang.String", valueCall.calculateResolvedType().describe());
    }

    @Test
    void resolveInheritedAnnotationAndObjectMethodsOnAnnotationVariable() {
        String code = "package hello;\n"
                + "@interface HasRoles {\n"
                + "    boolean skipCheck() default false;\n"
                + "}\n"
                + "class Main {\n"
                + "    void m(HasRoles hasRoles) {\n"
                + "        hasRoles.annotationType();\n"
                + "        hasRoles.toString();\n"
                + "        hasRoles.hashCode();\n"
                + "        hasRoles.equals(null);\n"
                + "        hasRoles.getClass();\n"
                + "    }\n"
                + "}";

        CompilationUnit cu = parse(code);

        MethodCallExpr annotationTypeCall = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("annotationType"))
                .get();
        assertEquals(
                "java.lang.annotation.Annotation.annotationType()",
                annotationTypeCall.resolve().getQualifiedSignature());

        MethodCallExpr toStringCall = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("toString"))
                .get();
        assertEquals(
                "java.lang.annotation.Annotation.toString()",
                toStringCall.resolve().getQualifiedSignature());
        assertEquals("java.lang.String", toStringCall.calculateResolvedType().describe());

        MethodCallExpr hashCodeCall = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("hashCode"))
                .get();
        assertEquals(
                "java.lang.annotation.Annotation.hashCode()",
                hashCodeCall.resolve().getQualifiedSignature());

        MethodCallExpr equalsCall = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("equals"))
                .get();
        assertEquals(
                "java.lang.annotation.Annotation.equals(java.lang.Object)",
                equalsCall.resolve().getQualifiedSignature());

        MethodCallExpr getClassCall = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("getClass"))
                .get();
        assertEquals("java.lang.Object.getClass()", getClassCall.resolve().getQualifiedSignature());
    }

    @Test
    void unknownMethodOrWrongArgumentsOnAnnotationDoesNotResolve() {
        String code = "package hello;\n"
                + "@interface HasRoles {\n"
                + "    boolean skipCheck() default false;\n"
                + "}\n"
                + "class Main {\n"
                + "    void m(HasRoles hasRoles) {\n"
                + "        hasRoles.unknown();\n"
                + "        hasRoles.skipCheck(true);\n"
                + "    }\n"
                + "}";

        CompilationUnit cu = parse(code);

        MethodCallExpr unknownCall = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("unknown"))
                .get();
        assertThrows(UnsolvedSymbolException.class, unknownCall::resolve);

        MethodCallExpr wrongArgsCall = cu.findFirst(
                        MethodCallExpr.class, m -> m.getNameAsString().equals("skipCheck"))
                .get();
        assertThrows(UnsolvedSymbolException.class, wrongArgsCall::resolve);
    }

    @Test
    void getDeclaredMethodsReturnsAnnotationElements() {
        String code = "@interface Marker {}\n"
                + "@interface WithElements {\n"
                + "    int CONSTANT = 1;\n"
                + "    String value();\n"
                + "    boolean flag() default false;\n"
                + "}";

        CompilationUnit cu = parse(code);

        ResolvedAnnotationDeclaration marker = cu.findFirst(
                        AnnotationDeclaration.class, a -> a.getNameAsString().equals("Marker"))
                .get()
                .resolve();
        assertEquals(Collections.emptySet(), marker.getDeclaredMethods());

        ResolvedAnnotationDeclaration withElements = cu.findFirst(
                        AnnotationDeclaration.class, a -> a.getNameAsString().equals("WithElements"))
                .get()
                .resolve();
        Set<String> signatures = withElements.getDeclaredMethods().stream()
                .map(ResolvedMethodDeclaration::getSignature)
                .collect(Collectors.toSet());
        assertEquals(new HashSet<>(Arrays.asList("value()", "flag()")), signatures);
    }
}
