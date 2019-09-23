/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StreamProvider;
import com.github.javaparser.ParserConfiguration.LanguageLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;

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
