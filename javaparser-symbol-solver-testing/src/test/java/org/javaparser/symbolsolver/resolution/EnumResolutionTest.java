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

import org.javaparser.ParserConfiguration;
import org.javaparser.StaticJavaParser;
import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.expr.FieldAccessExpr;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.ast.stmt.ReturnStmt;
import org.javaparser.ast.stmt.SwitchStmt;
import org.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.JavaSymbolSolver;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
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

}
