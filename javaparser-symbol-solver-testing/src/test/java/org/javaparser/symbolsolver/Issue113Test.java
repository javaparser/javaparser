/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package org.javaparser.symbolsolver;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.resolution.types.ResolvedReferenceType;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue113Test extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(adaptPath("src/test/resources/issue113"), new LeanParserConfiguration()));
    }

    @Test
    void issue113providedCodeDoesNotCrash() throws IOException {
        Path pathToSourceFile = adaptPath("src/test/resources/issue113/com/foo/Widget.java");
        CompilationUnit cu = parse(pathToSourceFile);

        JavaParserFacade parserFacade = JavaParserFacade.get(typeSolver);
        MethodDeclaration methodDeclaration = cu.findAll(MethodDeclaration.class).stream()
                .filter(node -> node.getName().getIdentifier().equals("doSomething")).findAny().orElse(null);
        methodDeclaration.findAll(MethodCallExpr.class).forEach(parserFacade::solve);
    }

    @Test
    void issue113superClassIsResolvedCorrectly() throws IOException {
        Path pathToSourceFile = adaptPath("src/test/resources/issue113/com/foo/Widget.java");
        CompilationUnit cu = parse(pathToSourceFile);

        JavaParserClassDeclaration jssExtendedWidget = new JavaParserClassDeclaration(cu.getClassByName("Widget").get(), typeSolver);
        ResolvedReferenceType superClass = jssExtendedWidget.getSuperClass();
        assertEquals("com.foo.base.Widget", superClass.getQualifiedName());
    }

}
