/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class EnumResolutionTest extends AbstractResolutionTest {

    @Test
    void switchOnEnum() {
        CompilationUnit cu = parseSample("SwitchOnEnum");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SwitchOnEnum");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        SwitchStmt switchStmt = Navigator.demandSwitch(method);
        Expression expression = switchStmt.getEntries().get(0).getLabels().get(0);

        SymbolReference<? extends ResolvedValueDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(expression);
        assertTrue(ref.isSolved());
        assertEquals("SwitchOnEnum.MyEnum", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    void enumAndStaticInitializer() {
        CompilationUnit cu = parseSample("EnumAndStaticInitializer");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        MethodCallExpr call = Navigator.findMethodCall(clazz, "put").get();

        ResolvedType ref = JavaParserFacade.get(new ReflectionTypeSolver()).getType(call);
        assertEquals("MyClass.Primitive", ref.describe());
    }

    // Related to issue 1699
    @Test
    void resolveEnumConstantAccess() {
        try {
            // configure symbol solver before parsing
            StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

            // parse compilation unit and get field access expression
            CompilationUnit cu = parseSample("EnumFieldAccess");
            ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "EnumFieldAccess");
            MethodDeclaration method = Navigator.demandMethod(clazz, "accessField");
            ReturnStmt returnStmt = (ReturnStmt) method.getBody().get().getStatements().get(0);
            FieldAccessExpr expression = returnStmt.getExpression().get().asFieldAccessExpr();

            // resolve field access expression
            ResolvedValueDeclaration resolvedValueDeclaration = expression.resolve();

            assertFalse(resolvedValueDeclaration.isField());
            assertTrue(resolvedValueDeclaration.isEnumConstant());

            ResolvedEnumConstantDeclaration resolvedEnumConstantDeclaration = resolvedValueDeclaration.asEnumConstant();
            assertEquals("SOME", resolvedEnumConstantDeclaration.getName());
            assertTrue(resolvedEnumConstantDeclaration.isEnumConstant());
            assertTrue(resolvedEnumConstantDeclaration.hasName());
        } finally {
            StaticJavaParser.setConfiguration(new ParserConfiguration());
        }
    }

    @Test
    void enumAccessSpecifier() {
        try {
            StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
            CompilationUnit cu = parseSample("EnumAccessSpecifier");
            ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");

            EnumDeclaration ed_public = Navigator.findType(clazz, "EnumPublic").get().toEnumDeclaration().get();
            assertEquals(AccessSpecifier.PUBLIC, ((JavaParserEnumDeclaration) ed_public.resolve()).accessSpecifier());

            EnumDeclaration ed_protected = Navigator.findType(clazz, "EnumProtected").get().toEnumDeclaration().get();
            assertEquals(AccessSpecifier.PROTECTED, ((JavaParserEnumDeclaration) ed_protected.resolve()).accessSpecifier());

            EnumDeclaration ed_private = Navigator.findType(clazz, "EnumPrivate").get().toEnumDeclaration().get();
            assertEquals(AccessSpecifier.PRIVATE, ((JavaParserEnumDeclaration) ed_private.resolve()).accessSpecifier());

            EnumDeclaration ed_default = Navigator.findType(clazz, "EnumDefault").get().toEnumDeclaration().get();
            assertEquals(AccessSpecifier.NONE, ((JavaParserEnumDeclaration) ed_default.resolve()).accessSpecifier());
        } finally {
            StaticJavaParser.setConfiguration(new ParserConfiguration());
        }
    }

    @Test
    public void testResolveValueOfMethod() {
        String s =
                "public class ClassTest {\n" +
                        "    public enum SecurityPolicyScopedTemplatesKeys {\n" +
                        "        SUSPICIOUS(\"suspicious\");\n" +
                        "        private String displayName;\n" +
                        "\n" +
                        "        private SecurityPolicyScopedTemplatesKeys(String displayName) {\n" +
                        "            this.displayName = displayName;\n" +
                        "        }\n" +
                        "\n" +
                        "        public String getDisplayName() {\n" +
                        "            return this.displayName;\n" +
                        "        }\n" +
                        "    }\n" +
                        "\n" +
                        "    public void m() {\n" +
                        "        SecurityPolicyScopedTemplatesKeys a = SecurityPolicyScopedTemplatesKeys.valueOf(\"SUSPICIOUS\");\n" +
                        "    }\n" +
                        "}";
        TypeSolver typeSolver = new ReflectionTypeSolver();
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = StaticJavaParser.parse(s);
        MethodCallExpr methodCallExpr = cu.findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration rd = methodCallExpr.resolve();
        assertEquals("valueOf", rd.getName());
        assertEquals("ClassTest.SecurityPolicyScopedTemplatesKeys", rd.getReturnType().describe());
        assertEquals(1, rd.getNumberOfParams());
        assertEquals("java.lang.String", rd.getParam(0).describeType());
    }

}
