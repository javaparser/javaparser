/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.BlockStmtContext;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

/**
 *
 */
class BlockStmtContextResolutionTest extends AbstractResolutionTest {

    @BeforeEach
    void setup() {
    }

    // issue #3526
    @Test
    void field_must_be_resolved_from_previous_declaration(){
        String src = "public class Example {\n"
                + "    int a = 3;\n"
                + "    public void bla() {\n"
                + "        a = 7; // 'a' must be resolved as int not String"
                + "        String a = \"\";\n"
                + "        a = \"test\";\n"
                + "    }\n"
                + "}";
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver())));
        StaticJavaParser.setConfiguration(configuration);
        CompilationUnit cu = StaticJavaParser.parse(src);
        BlockStmt stmt = cu.findFirst(BlockStmt.class).get();
        BlockStmtContext ctx = new BlockStmtContext(stmt, new ReflectionTypeSolver());
        SymbolReference<? extends ResolvedValueDeclaration> ref = ctx.solveSymbol("a");

        assertEquals(true, ref.isSolved());
        assertEquals("int", ref.getCorrespondingDeclaration().getType().asPrimitive().describe());
    }

}
