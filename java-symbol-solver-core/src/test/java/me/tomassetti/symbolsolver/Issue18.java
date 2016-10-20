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

package me.tomassetti.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.resolution.AbstractResolutionTest;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class Issue18 extends AbstractResolutionTest {

    @Test
    public void typeDeclarationSuperClassImplicitlyIncludeObject() throws ParseException {
        CompilationUnit cu = parseSample("Issue18");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Foo");
        MethodDeclaration methodDeclaration = Navigator.demandMethod(clazz, "bar");
        ExpressionStmt expr = (ExpressionStmt)methodDeclaration.getBody().get().getStmts().get(1);
        TypeSolver typeSolver = new JreTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        Type type = javaParserFacade.getType(expr.getExpression());
        assertEquals("java.lang.Object", type.describe());
    }
}
