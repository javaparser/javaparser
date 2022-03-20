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
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.AssociableToASTTest;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclarationTest;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapabilityTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import java.util.Optional;

class JavaParserMethodDeclarationTest implements ResolvedMethodDeclarationTest, TypeVariableResolutionCapabilityTest,
        AssociableToASTTest<MethodDeclaration> {

    @Override
    public Optional<MethodDeclaration> getWrappedDeclaration(AssociableToAST<MethodDeclaration> associableToAST) {
        return Optional.of(
                safeCast(associableToAST, JavaParserMethodDeclaration.class).getWrappedNode()
        );
    }

    @Override
    public JavaParserMethodDeclaration createValue() {
        MethodDeclaration methodDeclaration = StaticJavaParser.parse("class A {void a() {}}")
                .findFirst(MethodDeclaration.class).get();
        TypeSolver typeSolver = new ReflectionTypeSolver();
        return new JavaParserMethodDeclaration(methodDeclaration, typeSolver);
    }

}
