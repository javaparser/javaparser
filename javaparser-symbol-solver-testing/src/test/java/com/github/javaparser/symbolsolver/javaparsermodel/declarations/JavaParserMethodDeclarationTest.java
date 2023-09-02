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

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclarationTest;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapabilityTest;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.CodeGenerationUtils;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.*;

class JavaParserMethodDeclarationTest extends AbstractResolutionTest
		implements ResolvedMethodDeclarationTest, TypeVariableResolutionCapabilityTest {

    @Override
    public Optional<Node> getWrappedDeclaration(AssociableToAST associableToAST) {
        return Optional.of(
                safeCast(associableToAST, JavaParserMethodDeclaration.class).getWrappedNode()
        );
    }

    @Override
    public JavaParserMethodDeclaration createValue() {
        MethodDeclaration methodDeclaration = StaticJavaParser.parse("class A {void a() {}}")
                .findFirst(MethodDeclaration.class).get();
        TypeSolver typeSolver = new ReflectionTypeSolver();
        return new JavaParserMethodDeclaration(methodDeclaration, typeSolver);
    }

    @Test
    void checkModifiersOnInterfaceMethods() throws IOException {
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        Path rootDir = CodeGenerationUtils.mavenModuleRoot(JavaParserFieldDeclarationTest.class).resolve("src/test/java/com/github/javaparser/symbolsolver/testingclasses");
        CompilationUnit cu = parse(rootDir.resolve("InterfaceWithMethods.java"));
        ResolvedMethodDeclaration method1 = new JavaParserMethodDeclaration(cu.findAll(MethodDeclaration.class).get(0), reflectionTypeSolver);

        assertTrue(method1.hasModifier(Modifier.Keyword.PUBLIC));
        assertFalse(method1.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(method1.hasModifier(Modifier.Keyword.FINAL));
        assertTrue(method1.hasModifier(Modifier.Keyword.ABSTRACT));
        assertFalse(method1.hasModifier(Modifier.Keyword.DEFAULT));

        ResolvedMethodDeclaration method2 = new JavaParserMethodDeclaration(cu.findAll(MethodDeclaration.class).get(1), reflectionTypeSolver);

        assertTrue(method2.hasModifier(Modifier.Keyword.PUBLIC));
        assertFalse(method2.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(method2.hasModifier(Modifier.Keyword.FINAL));
        assertTrue(method2.hasModifier(Modifier.Keyword.ABSTRACT));
        assertFalse(method2.hasModifier(Modifier.Keyword.DEFAULT));

        ResolvedMethodDeclaration method3 = new JavaParserMethodDeclaration(cu.findAll(MethodDeclaration.class).get(2), reflectionTypeSolver);

        assertTrue(method3.hasModifier(Modifier.Keyword.PUBLIC));
        assertFalse(method3.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(method3.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(method3.hasModifier(Modifier.Keyword.ABSTRACT));
        assertTrue(method3.hasModifier(Modifier.Keyword.DEFAULT));

        ResolvedMethodDeclaration method4 = new JavaParserMethodDeclaration(cu.findAll(MethodDeclaration.class).get(3), reflectionTypeSolver);

        assertTrue(method4.hasModifier(Modifier.Keyword.PUBLIC));
        assertTrue(method4.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(method4.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(method4.hasModifier(Modifier.Keyword.ABSTRACT));
        assertFalse(method4.hasModifier(Modifier.Keyword.DEFAULT));
    }

    @Test
    void checkModifiersOnClassMethods() throws IOException {
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        Path rootDir = CodeGenerationUtils.mavenModuleRoot(JavaParserFieldDeclarationTest.class).resolve("src/test/java/com/github/javaparser/symbolsolver/testingclasses");
        CompilationUnit cu = parse(rootDir.resolve("ClassWithMethods.java"));

        ResolvedMethodDeclaration method1 = new JavaParserMethodDeclaration(cu.findAll(MethodDeclaration.class).get(0), reflectionTypeSolver);

        assertFalse(method1.hasModifier(Modifier.Keyword.PUBLIC));
        assertFalse(method1.hasModifier(Modifier.Keyword.PRIVATE));
        assertFalse(method1.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(method1.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(method1.hasModifier(Modifier.Keyword.ABSTRACT));
        assertFalse(method1.hasModifier(Modifier.Keyword.DEFAULT));

        ResolvedMethodDeclaration method2 = new JavaParserMethodDeclaration(cu.findAll(MethodDeclaration.class).get(1), reflectionTypeSolver);

        assertTrue(method2.hasModifier(Modifier.Keyword.PUBLIC));
        assertFalse(method1.hasModifier(Modifier.Keyword.PRIVATE));
        assertFalse(method2.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(method2.hasModifier(Modifier.Keyword.FINAL));
        assertTrue(method2.hasModifier(Modifier.Keyword.ABSTRACT));
        assertFalse(method2.hasModifier(Modifier.Keyword.DEFAULT));

        ResolvedMethodDeclaration method3 = new JavaParserMethodDeclaration(cu.findAll(MethodDeclaration.class).get(2), reflectionTypeSolver);

        assertTrue(method3.hasModifier(Modifier.Keyword.PUBLIC));
        assertFalse(method1.hasModifier(Modifier.Keyword.PRIVATE));
        assertTrue(method3.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(method3.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(method3.hasModifier(Modifier.Keyword.ABSTRACT));
        assertFalse(method3.hasModifier(Modifier.Keyword.DEFAULT));

        ResolvedMethodDeclaration method4 = new JavaParserMethodDeclaration(cu.findAll(MethodDeclaration.class).get(3), reflectionTypeSolver);

        assertFalse(method4.hasModifier(Modifier.Keyword.PUBLIC));
        assertTrue(method4.hasModifier(Modifier.Keyword.PRIVATE));
        assertFalse(method4.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(method4.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(method4.hasModifier(Modifier.Keyword.ABSTRACT));
        assertFalse(method4.hasModifier(Modifier.Keyword.DEFAULT));
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
    @Test
	void issue2484() {
		String code =
				"public class MyClass {\n"
						+ "    private Ibaz m_something;\n"
						+ "\n"
						+ "    public interface Ibaz {\n"
						+ "    }\n"
						+ "    \n"
						+ "    public void foo(Class<? extends Ibaz> clazz) {\n"
						+ "    }\n"
						+ "    \n"
						+ "    protected void bar() {\n"
						+ "        foo(null); // this works\n"
						+ "        foo(m_something.getClass()); // this doesn't work\n"
						+ "    }\n"
						+ "}";

		JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));
		CompilationUnit cu = parser.parse(code);

		List<MethodCallExpr> mces = cu.findAll(MethodCallExpr.class);
		assertEquals("MyClass.foo(java.lang.Class<? extends MyClass.Ibaz>)", mces.get(0).resolve().getQualifiedSignature());
		assertEquals("MyClass.foo(java.lang.Class<? extends MyClass.Ibaz>)", mces.get(1).resolve().getQualifiedSignature());
	}

}
