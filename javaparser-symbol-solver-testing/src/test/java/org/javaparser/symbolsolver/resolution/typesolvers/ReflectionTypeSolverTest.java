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

package org.javaparser.symbolsolver.resolution.typesolvers;

import org.javaparser.JavaParser;
import org.javaparser.ParseStart;
import org.javaparser.ParserConfiguration;
import org.javaparser.StreamProvider;
import org.javaparser.ParserConfiguration.LanguageLevel;
import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.expr.ObjectCreationExpr;
import org.javaparser.ast.visitor.VoidVisitorAdapter;
import org.javaparser.resolution.UnsolvedSymbolException;
import org.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import org.javaparser.symbolsolver.JavaSymbolSolver;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.Assertions;

class ReflectionTypeSolverTest extends AbstractSymbolResolutionTest {

    @Test
    void testHasType() {
        ReflectionTypeSolver ts = new ReflectionTypeSolver();
        assertEquals(true, ts.hasType(String.class.getCanonicalName()));
        assertEquals(true, ts.hasType(Object.class.getCanonicalName()));
        assertEquals(false, ts.hasType("foo.zum.unexisting"));
    }
    
    @Test()
    void testInvalidArgumentNumber() throws IOException {
        Path file = adaptPath("src/test/resources/issue2366/Test.java");

        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(new ReflectionTypeSolver());	    

        ParserConfiguration pc = new ParserConfiguration()
            	                        .setSymbolResolver(new JavaSymbolSolver(combinedSolver))
            	                        .setLanguageLevel(LanguageLevel.JAVA_8);

        JavaParser javaParser = new JavaParser(pc);

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();
        
        Assertions.assertThrows(UnsolvedSymbolException.class, () -> unit.accept(new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(ObjectCreationExpr exp, Object arg) {
            	super.visit(exp, arg);
                exp.resolve().getSignature();
            }            
        }, null));
    }

}
