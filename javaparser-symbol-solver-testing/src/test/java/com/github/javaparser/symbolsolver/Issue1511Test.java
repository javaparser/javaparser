/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.FileNotFoundException;
import java.nio.file.Path;

import static com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest.adaptPath;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * IndexOutOfBoundsException when attempting to resolve super() #1511
 *
 * @see <a href="https://github.com/javaparser/javaparser/issues/1511">https://github.com/javaparser/javaparser/issues/1511</a>
 */
public class Issue1511Test {

    @Test
    public void test() throws FileNotFoundException {

        Path dir = adaptPath("src/test/resources/issue1511");
        Path file = adaptPath("src/test/resources/issue1511/A.java");

        // configure symbol solver
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(dir.toFile()));
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
        StaticJavaParser.getConfiguration().setSymbolResolver(symbolSolver);

        // get compilation unit & extract explicit constructor invocation statement
        CompilationUnit cu = StaticJavaParser.parse(file.toFile());
        ExplicitConstructorInvocationStmt ecis = cu.getPrimaryType().orElseThrow(IllegalStateException::new)
            .asClassOrInterfaceDeclaration().getMember(0)
            .asConstructorDeclaration().getBody().getStatement(0)
            .asExplicitConstructorInvocationStmt();

        // attempt to resolve explicit constructor invocation statement
        ResolvedConstructorDeclaration rcd = ecis.resolve(); //.resolveInvokedConstructor(); // <-- exception occurs
    }


    @Test
    public void exploratory_resolveAndGetSuperClass() {

        ParserConfiguration configuration = new ParserConfiguration();
        configuration.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        JavaParser javaParser = new JavaParser(configuration);

        CompilationUnit foo = javaParser.parse("class A {}").getResult().orElseThrow(IllegalStateException::new);
        ResolvedReferenceType a = foo.getClassByName("A").orElseThrow(IllegalStateException::new).resolve().asClass().getSuperClass().get();

        assertEquals("java.lang.Object", a.getQualifiedName());
    }

}
