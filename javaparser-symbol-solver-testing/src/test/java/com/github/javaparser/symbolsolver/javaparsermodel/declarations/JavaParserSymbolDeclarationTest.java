/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.*;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserSymbolDeclarationTest {

    private final TypeSolver typeSolver = new ReflectionTypeSolver();

    /**
     * Try to create a field using {@link JavaParserSymbolDeclaration#field(VariableDeclarator, TypeSolver)} and check
     * if the returned declaration is marked as a field and can be converted to a
     * {@link com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration} using {@link ResolvedValueDeclaration#asField()}.
     */
    @Test
    void createdFieldShouldBeMarkedAsField() {
        VariableDeclarator variableDeclarator = parseBodyDeclaration("private final int x = 0;")
                .asFieldDeclaration()
                .getVariable(0);
        ResolvedValueDeclaration field = JavaParserSymbolDeclaration.field(variableDeclarator, typeSolver);

        assertTrue(field.isField());
        assertDoesNotThrow(field::asField);
    }

    /**
     * Try to create a parameter using {@link JavaParserSymbolDeclaration#parameter(Parameter, TypeSolver)} and check
     * if the returned declaration is marked as a parameter and can be converted to a
     * {@link com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration} using {@link ResolvedValueDeclaration#asParameter()}.
     */
    @Test
    void createdParameterShouldBeMarkedAsParameter() {
        Parameter parameter = parseParameter("String myStr");;
        ResolvedValueDeclaration parameterDeclaration = JavaParserSymbolDeclaration.parameter(parameter, typeSolver);

        assertTrue(parameterDeclaration.isParameter());
        assertDoesNotThrow(parameterDeclaration::asParameter);
    }

    /**
     * Try to create a local variable using {@link JavaParserSymbolDeclaration#localVar(VariableDeclarator, TypeSolver)}
     * and check if the returned declaration is marked as a variable.
     */
    @Test
    void createdLocalVariableShouldBeMarkedAsVariable() {
        VariableDeclarator variableDeclarator = parseVariableDeclarationExpr("int x = 0").getVariable(0);
        ResolvedValueDeclaration localVar = JavaParserSymbolDeclaration.localVar(variableDeclarator, typeSolver);

        assertTrue(localVar.isVariable());
    }

    /**
     * Try to create a pattern variable using {@link JavaParserSymbolDeclaration#patternVar(PatternExpr, TypeSolver)} and check
     * if the returned declaration is marked as a pattern and can be converted to a
     * {@link com.github.javaparser.resolution.declarations.ResolvedPatternDeclaration} using {@link ResolvedValueDeclaration#asPattern()}.
     */
    @Test
    void createdPatternVariableShouldBeMarkedAsPatternVar() {
        PatternExpr patternExpr = new PatternExpr();
        ResolvedValueDeclaration patternVar = JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver);

        assertTrue(patternVar.isPattern());
        assertDoesNotThrow(patternVar::asPattern);
    }

}
