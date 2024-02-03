/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.utils.Pair;

public class Issue3184Test extends AbstractResolutionTest {

	@Test
	void test() {
		String code = "public class Program {\n" +
		        "\n" +
		        "    public static class InnerClass<T> {\n" +
		        "       void method1() {\n" +
		        "           new InnerClass<T>();\n" + // Buggy
		        "       }\n" +
		        "       <T1> void method2() {\n" +
		        "           new InnerClass<T1>();\n" + // OK
		        "           new InnerClass<T>();\n" + // Buggy
		        "       }\n" +
		        "    }\n" +
		        "}";

		CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver())).parse(code);
		List<ObjectCreationExpr> objCrtExprs = cu.findAll(ObjectCreationExpr.class);
		objCrtExprs.forEach(expr -> {
		    ResolvedType resRefType = expr.getType().resolve();
		    ResolvedReferenceTypeDeclaration resRefTypeDecl = resRefType.asReferenceType().getTypeDeclaration().get();
		    List<ResolvedTypeParameterDeclaration> resTypeParamsDecl = resRefTypeDecl.getTypeParameters();
		    List<Pair<ResolvedTypeParameterDeclaration, ResolvedType>> resTypeParamsDeclMap = resRefType.asReferenceType().getTypeParametersMap();
		    assertFalse(resTypeParamsDecl.isEmpty());
		    assertFalse(resTypeParamsDeclMap.isEmpty());
		    for (Pair<ResolvedTypeParameterDeclaration, ResolvedType> resTypeParamsDeclPair : resTypeParamsDeclMap) {
		        assertTrue(resTypeParamsDeclPair.b.isTypeVariable());
		    }
		});
	}
}
