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
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.resolution.UnsolvedSymbolException;
import org.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertThrows;

class UnknownMethodsResolutionTest extends AbstractResolutionTest {

	@Test
	void testUnknownMethod1() {
		assertThrows(UnsolvedSymbolException.class, () -> {
		    CompilationUnit cu = parseSample("UnknownMethods");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "UnknownMethods");
		MethodDeclaration method = Navigator.demandMethod(clazz, "test1");
		MethodCallExpr methodCallExpr = method.getBody().get().getStatement(0).asExpressionStmt().getExpression().asMethodCallExpr();
		SymbolReference<ResolvedMethodDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(methodCallExpr);
});
						
}

	@Test
	void testUnknownMethod2() {
		assertThrows(UnsolvedSymbolException.class, () -> {
		    CompilationUnit cu = parseSample("UnknownMethods");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "UnknownMethods");
		MethodDeclaration method = Navigator.demandMethod(clazz, "test2");
		MethodCallExpr methodCallExpr = method.getBody().get().getStatement(1).asExpressionStmt().getExpression().asMethodCallExpr();
		SymbolReference<ResolvedMethodDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(methodCallExpr);
});
						
}
}
