/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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
