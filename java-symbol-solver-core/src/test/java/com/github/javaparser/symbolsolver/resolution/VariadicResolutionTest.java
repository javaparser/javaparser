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

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;

public class VariadicResolutionTest extends AbstractResolutionTest {

    @Test
    public void issue7() throws ParseException {
        CompilationUnit cu = parseSample("Generics_issue7");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo3");

        ReturnStmt stmt = (ReturnStmt) method.getBody().get().getStmts().get(0);
        Expression expression = stmt.getExpr().get();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(new JreTypeSolver());
        Type type = javaParserFacade.getType(expression);
        assertEquals(true, type.isReferenceType());
        assertEquals(List.class.getCanonicalName(), type.asReferenceType().getQualifiedName());
        assertEquals("java.util.List<java.lang.Long>", type.describe());
    }

}
