/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.AssociableToASTTest;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclarationTest;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import java.util.Optional;

class JavaParserParameterDeclarationTest implements ResolvedParameterDeclarationTest, AssociableToASTTest<Parameter> {

    @Override
    public Optional<Parameter> getWrappedDeclaration(AssociableToAST<Parameter> associableToAST) {
        return Optional.of(
                safeCast(associableToAST, JavaParserParameterDeclaration.class).getWrappedNode()
        );
    }

    @Override
    public JavaParserParameterDeclaration createValue() {
        Parameter parameter = StaticJavaParser.parseMethodDeclaration("<T> void a(T a) {}")
                .findFirst(Parameter.class).get();
        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        return new JavaParserParameterDeclaration(parameter, typeSolver);
    }

    @Override
    public String getCanonicalNameOfExpectedType(ResolvedValueDeclaration resolvedDeclaration) {
        return "T";
    }
}
