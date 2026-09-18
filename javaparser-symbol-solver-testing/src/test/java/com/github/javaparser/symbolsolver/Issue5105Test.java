/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * A call qualified by a type resolves against the members of that type. Static imports are not
 * transitive (JLS 7.5.3, 7.5.4), so the ones written in the file that declares the receiver type
 * do not add members to it: {@code Mid.ping()} is a compile error when {@code Mid.java} merely
 * imports {@code ping} from elsewhere.
 */
public class Issue5105Test extends AbstractSymbolResolutionTest {

    private Path issueResourcesPath;
    private JavaParser parser;
    private CompilationUnit cu;

    @BeforeEach
    void parseOuter() throws IOException {
        issueResourcesPath = adaptPath("src/test/resources/issue5105");
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(issueResourcesPath));
        parser = new JavaParser(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)));
        cu = parse("qq/Outer.java");
    }

    private CompilationUnit parse(String file) throws IOException {
        return parser.parse(issueResourcesPath.resolve(file)).getResult().get();
    }

    @Test
    void aCallQualifiedByATypeDoesNotSeeThatFilesStaticImports() {
        MethodCallExpr call = callIn("qualifiedByType");

        assertThrows(UnsolvedSymbolException.class, call::resolve);
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
    }

    @Test
    void aCallQualifiedByAnInstanceDoesNotSeeThatFilesStaticImports() {
        MethodCallExpr call = callIn("qualifiedByInstance");

        assertThrows(UnsolvedSymbolException.class, call::resolve);
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
    }

    @Test
    void aMethodReferenceDoesNotSeeThatFilesStaticImports() {
        MethodReferenceExpr methodReference =
                cu.findAll(MethodReferenceExpr.class).stream().findFirst().get();

        assertThrows(UnsolvedSymbolException.class, methodReference::resolve);
    }

    @Test
    void anInstanceMethodOfTheReceiverTypeStillResolves() {
        MethodCallExpr call = callIn("instanceMethodOfTheDeclaringType");

        assertEquals("qq.Sink.inst()", call.resolve().getQualifiedSignature());
        assertEquals("java.lang.String", call.calculateResolvedType().describe());
    }

    @Test
    void aStaticMethodOfTheReceiverTypeStillResolves() {
        MethodCallExpr call = callIn("staticMethodOfTheDeclaringType");

        assertEquals("qq.Sink.ping()", call.resolve().getQualifiedSignature());
        assertEquals("java.lang.String", call.calculateResolvedType().describe());
    }

    @Test
    void anUnqualifiedCallStillSeesItsOwnFilesStaticImports() throws IOException {
        // The same rule seen from the other side: written inside Lexical.java, the bare name ping is a
        // lexical lookup, and that file's own static imports do apply to it.
        CompilationUnit lexical = parse("qq/Lexical.java");
        MethodCallExpr call = lexical.findFirst(MethodCallExpr.class).get();

        assertEquals("qq.Sink.ping()", call.resolve().getQualifiedSignature());
        assertEquals("java.lang.String", call.calculateResolvedType().describe());
    }

    private MethodCallExpr callIn(String methodName) {
        MethodDeclaration method = cu.findAll(MethodDeclaration.class).stream()
                .filter(it -> it.getNameAsString().equals(methodName))
                .findFirst()
                .get();
        return method.findFirst(MethodCallExpr.class).get();
    }
}
