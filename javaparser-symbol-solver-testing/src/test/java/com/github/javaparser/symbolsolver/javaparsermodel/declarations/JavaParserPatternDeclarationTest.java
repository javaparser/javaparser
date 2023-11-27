/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedPatternDeclarationTest;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeAll;

import java.util.Optional;

class JavaParserPatternDeclarationTest implements ResolvedPatternDeclarationTest {

    @BeforeAll
    public static void setup() {
        StaticJavaParser.getConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW);
    }

    @Override
    public Optional<Node> getWrappedDeclaration(AssociableToAST associableToAST) {
        return Optional.of(
                safeCast(associableToAST, JavaParserPatternDeclaration.class).getWrappedNode()
        );
    }

    @Override
    public JavaParserPatternDeclaration createValue() {
        PatternExpr wrappedNode = StaticJavaParser.parse("class A {a() {if (object instanceof String d) return;}}")
                .findFirst(PatternExpr.class).get();
        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        return new JavaParserPatternDeclaration(wrappedNode, typeSolver);
    }

    @Override
    public String getCanonicalNameOfExpectedType(ResolvedValueDeclaration resolvedDeclaration) {
        return String.class.getCanonicalName();
    }
}
