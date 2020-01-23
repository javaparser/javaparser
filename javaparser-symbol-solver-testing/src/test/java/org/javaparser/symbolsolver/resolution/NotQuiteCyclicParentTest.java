/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package org.javaparser.symbolsolver.resolution;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.expr.VariableDeclarationExpr;
import org.javaparser.ast.stmt.ExpressionStmt;
import org.javaparser.resolution.UnsolvedSymbolException;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
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
