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
 * This file is part of JavaParser is provided in both LICENCE.LGPL and
 * LICENCE.APACHE files. JavaParser is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 */

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import org.junit.jupiter.api.Test;

public class Issue5105Test extends AbstractSymbolResolutionTest {

    private List<MethodCallExpr> calls() throws IOException {
        Path issueResourcesPath = adaptPath("src/test/resources/issue5105");
        ReflectionTypeSolver rts = new ReflectionTypeSolver();
        JavaParserTypeSolver jpts = new JavaParserTypeSolver(issueResourcesPath);
        CombinedTypeSolver cts = new CombinedTypeSolver();
        cts.add(rts);
        cts.add(jpts);
        ParserConfiguration pc = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(cts));
        StaticJavaParser.setConfiguration(pc);
        CompilationUnit cu = StaticJavaParser.parse(issueResourcesPath.resolve("qq/Outer.java"));
        return cu.findAll(MethodCallExpr.class);
    }

    @Test
    public void qualifiedCallDoesNotUseReceiverTypeStaticImports() throws IOException {
        // Mid declares nothing; the static import lives in Mid.java, not in Outer.java,
        // so Mid.ping() has no member to resolve to (JLS 7.5.3/7.5.4: static imports
        // are not transitive)
        MethodCallExpr call = calls().stream()
                .filter(c -> c.getNameAsString().equals("ping")
                        && c.getScope().isPresent()
                        && c.getScope().get().isNameExpr())
                .findAny()
                .get();
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @Test
    public void instanceQualifiedCallDoesNotUseReceiverTypeStaticImports() throws IOException {
        // same rule for a call qualified by an instance of the receiver type
        MethodCallExpr call = calls().stream()
                .filter(c -> c.getNameAsString().equals("ping")
                        && c.getScope().isPresent()
                        && c.getScope().get().isObjectCreationExpr())
                .findAny()
                .get();
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @Test
    public void subclassQualifiedCallDoesNotUseSuperclassTypeStaticImports() throws IOException {
        // MidSub extends Mid and Mid only statically imports Sink.ping();
        // the inherited-member lookup must not escape into Mid.java's imports
        // either (JLS 7.5.3/7.5.4)
        MethodCallExpr call = calls().stream()
                .filter(c -> c.getNameAsString().equals("ping")
                        && c.getScope().isPresent()
                        && c.getScope().get().isNameExpr()
                        && c.getScope().get().asNameExpr().getNameAsString().equals("MidSub"))
                .findAny()
                .get();
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @Test
    public void inheritedStaticMemberViaSubclassStillResolves() throws IOException {
        // Deep extends Sink and inherits its static ping(); a member lookup
        // must still find inherited members
        MethodCallExpr call = calls().stream()
                .filter(c -> c.getNameAsString().equals("ping")
                        && c.getScope().isPresent()
                        && c.getScope().get().isNameExpr()
                        && c.getScope().get().asNameExpr().getNameAsString().equals("Deep"))
                .findAny()
                .get();
        assertEquals("qq.Sink.ping()", call.resolve().getQualifiedSignature());
    }

    @Test
    public void instanceCallOnRealMemberStillResolves() throws IOException {
        // control: an instance method that is genuinely declared on the receiver
        MethodCallExpr call = calls().stream()
                .filter(c -> c.getNameAsString().equals("inst"))
                .findAny()
                .get();
        assertEquals("qq.Sink.inst()", call.resolve().getQualifiedSignature());
    }
}
