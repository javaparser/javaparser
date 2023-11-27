/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class VariableResolutionTest extends AbstractResolutionTest {

	@Test
	void variableResolutionNoBlockStmt() {
		// Test without nested block statement

		CompilationUnit cu = parseSample("VariableResolutionInVariousScopes");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VariableResolutionInVariousScopes");

		MethodDeclaration method = Navigator.demandMethod(clazz, "noBlock");
		MethodCallExpr callExpr = method.findFirst(MethodCallExpr.class).get();
		MethodUsage methodUsage = JavaParserFacade.get(new ReflectionTypeSolver()).solveMethodAsUsage(callExpr);

		assertTrue(methodUsage.declaringType().getQualifiedName().equals("java.lang.String"));
	}

	@Test
	void variableResolutionWithBlockStmt() {
		// Test without nested block statement

		CompilationUnit cu = parseSample("VariableResolutionInVariousScopes");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VariableResolutionInVariousScopes");

		MethodDeclaration method = Navigator.demandMethod(clazz, "withBlock");
		MethodCallExpr callExpr = method.findFirst(MethodCallExpr.class).get();
		MethodUsage methodUsage = JavaParserFacade.get(new ReflectionTypeSolver()).solveMethodAsUsage(callExpr);

		assertTrue(methodUsage.declaringType().getQualifiedName().equals("java.lang.String"));
	}
}
