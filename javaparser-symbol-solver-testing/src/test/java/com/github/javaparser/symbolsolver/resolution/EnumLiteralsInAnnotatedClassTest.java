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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StreamProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class EnumLiteralsInAnnotatedClassTest {

    @Test
    void resolveFieldOfEnumAsInternalClassOfClassUnqualifiedSamePackage() throws IOException {
        File src = new File("src/test/resources/enumLiteralsInAnnotatedClass");
        File aClass = new File(src.getPath() + File.separator + "foo" + File.separator + "bar"
                + File.separator + "AClass.java");

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(src));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser parser = new JavaParser(parserConfiguration);
        StreamProvider classProvider = new StreamProvider(new FileInputStream(aClass), StandardCharsets.UTF_8.name());

        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, classProvider).getResult().get();
        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("BinaryExpr.Operator.OR") && n.getRange().get().begin.line == 4);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("OR", fae.get().resolve().getName());
    }

    @Test
    void resolveFieldOfEnumAsInternalClassOfClassQualifiedSamePackage() throws IOException {
        File src = new File("src/test/resources/enumLiteralsInAnnotatedClass");
        File aClass = new File(src.getPath() + File.separator + "foo" + File.separator + "bar"
                + File.separator + "AClass.java");

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(src));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser parser = new JavaParser(parserConfiguration);
        StreamProvider classProvider = new StreamProvider(new FileInputStream(aClass), StandardCharsets.UTF_8.name());

        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, classProvider).getResult().get();
        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("foo.bar.BinaryExpr.Operator.AND") && n.getRange().get().begin.line == 5);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("AND", fae.get().resolve().getName());
    }

    @Test
    void resolveFieldOfEnumAsInternalClassOfClassUnqualifiedDifferentPackage() throws IOException {
        File src = new File("src/test/resources/enumLiteralsInAnnotatedClass");
        File aClass = new File(src.getPath() + File.separator + "foo" + File.separator + "bar"
                + File.separator + "differentpackage" + File.separator + "AClass2.java");

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(src));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser parser = new JavaParser(parserConfiguration);
        StreamProvider classProvider = new StreamProvider(new FileInputStream(aClass), StandardCharsets.UTF_8.name());

        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, classProvider).getResult().get();
        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("BinaryExpr.Operator.OR") && n.getRange().get().begin.line == 6);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("OR", fae.get().resolve().getName());
    }

    @Test
    void resolveFieldOfEnumAsInternalClassOfClassQualifiedDifferentPackage() throws IOException {
        File src = new File("src/test/resources/enumLiteralsInAnnotatedClass");
        File aClass = new File(src.getPath() + File.separator + "foo" + File.separator + "bar"
                + File.separator + "differentpackage" + File.separator + "AClass2.java");

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(src));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser parser = new JavaParser(parserConfiguration);
        StreamProvider classProvider = new StreamProvider(new FileInputStream(aClass), StandardCharsets.UTF_8.name());

        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, classProvider).getResult().get();
        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("foo.bar.BinaryExpr.Operator.AND") && n.getRange().get().begin.line == 7);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("AND", fae.get().resolve().getName());
    }
}
