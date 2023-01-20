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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.fail;

public class NotQuiteCyclicParentTest extends AbstractResolutionTest {

	@Test
	void testSimilarNameInterface() {
		CompilationUnit cu = parseSample("NotQuiteCyclicParent");
		ClassOrInterfaceDeclaration clazz = Navigator.demandInterface(cu, "NotQuiteCyclicParent");
		MethodDeclaration method = Navigator.demandMethod(clazz, "main");
		VariableDeclarationExpr varDec =
				(VariableDeclarationExpr) ((ExpressionStmt) method.getBody().get().getStatement(0)).getExpression();

		try {
			ResolvedType ref = JavaParserFacade.get(new ReflectionTypeSolver()).getType(varDec);
		} catch (UnsolvedSymbolException e) {
			return;
		}

		fail("We shouldn't be able to resolve the type (it is not defined).");
	}

}
