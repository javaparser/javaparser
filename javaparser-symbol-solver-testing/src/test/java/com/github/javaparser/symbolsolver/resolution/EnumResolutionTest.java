/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class EnumResolutionTest extends AbstractResolutionTest {

    @Test
    void switchOnEnum() {
        CompilationUnit cu = parseSample("SwitchOnEnum");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SwitchOnEnum");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        SwitchStmt switchStmt = Navigator.findSwitch(method);
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
