/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package org.javaparser.symbolsolver;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.ast.stmt.ExpressionStmt;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class Issue251Test extends AbstractResolutionTest{

    @Test
    void testSolveStaticallyImportedMemberType() {
        CompilationUnit cu = parseSample("Issue251");
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "Main");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        MethodDeclaration m = Navigator.demandMethod(cls, "bar");
        ExpressionStmt stmt = (ExpressionStmt) m.getBody().get().getStatements().get(1);
        MethodCallExpr expression = (MethodCallExpr) stmt.getExpression();
        Assertions.assertNotNull(javaParserFacade.solve(expression));
    }
}
