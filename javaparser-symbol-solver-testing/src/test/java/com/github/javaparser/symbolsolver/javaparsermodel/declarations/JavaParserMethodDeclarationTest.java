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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclarationTest;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapabilityTest;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

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
