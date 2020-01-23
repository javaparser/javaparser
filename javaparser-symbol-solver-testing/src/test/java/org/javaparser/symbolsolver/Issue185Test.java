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
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertNotNull;


class Issue185Test extends AbstractResolutionTest {

    @Test
    void testIssue() throws IOException {
        Path src = adaptPath("src/test/resources/recursion-issue");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        combinedTypeSolver.add(new ReflectionTypeSolver());
        CompilationUnit agendaCu = parse(adaptPath("src/test/resources/recursion-issue/Usage.java"));
        MethodCallExpr foo = Navigator.findMethodCall(agendaCu, "foo").get();
        assertNotNull(foo);
        JavaParserFacade.get(combinedTypeSolver).getType(foo);
    }

}
