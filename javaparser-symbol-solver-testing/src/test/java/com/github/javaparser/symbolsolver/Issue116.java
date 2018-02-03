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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class Issue116 extends AbstractResolutionTest {

    @Test
    public void arrayTypeIsNotPartOfTheTree() {
        CompilationUnit cu = parseSample("Issue116");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "JavaTest");
        MethodDeclaration methodDeclaration = Navigator.demandMethod(clazz, "foo");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        com.github.javaparser.ast.type.Type typeNode = methodDeclaration.getParameters().get(0).getType();
        ResolvedType type = javaParserFacade.convert(typeNode, typeNode);
        assertEquals("java.lang.String[]", type.describe());

        ExpressionStmt expressionStmt = (ExpressionStmt) methodDeclaration.getBody().get().getStatements().get(0);
        Expression argRef = expressionStmt.getExpression();
        assertEquals("java.lang.String[]", javaParserFacade.getType(argRef).describe());
    }
}
