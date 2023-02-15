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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue314Test extends AbstractResolutionTest{

    private TypeSolver typeResolver;
    private JavaParserFacade javaParserFacade;

    private ResolvedType getExpressionType(TypeSolver typeSolver, Expression expression) {
        return JavaParserFacade.get(typeSolver).getType(expression);
    }

    @BeforeEach
    void setup() {
        typeResolver = new ReflectionTypeSolver();
        javaParserFacade = JavaParserFacade.get(typeResolver);
    }

    @Test
    void resolveReferenceToFieldInheritedByInterface() {
        String code = "package foo.bar;\n"+
                "interface  A {\n" +
                "        int a = 0;\n" +
                "    }\n" +
                "    \n" +
                "    class B implements A {\n" +
                "        int getA() {\n" +
                "            return a;\n" +
                "        }\n" +
                "    }";
        CompilationUnit cu = parse(code);
        NameExpr refToA = Navigator.findNameExpression(Navigator.demandClass(cu, "B"), "a").get();
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = javaParserFacade.solve(refToA);
        assertEquals(true, symbolReference.isSolved());
        assertEquals(true, symbolReference.getCorrespondingDeclaration().isField());
        assertEquals("a", symbolReference.getCorrespondingDeclaration().getName());
    }



}
