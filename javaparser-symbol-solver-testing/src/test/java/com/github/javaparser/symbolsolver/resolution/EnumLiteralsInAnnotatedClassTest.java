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
        StreamProvider classProvider = new StreamProvider(new FileInputStream(aClass));

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
        StreamProvider classProvider = new StreamProvider(new FileInputStream(aClass));

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
        StreamProvider classProvider = new StreamProvider(new FileInputStream(aClass));

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
        StreamProvider classProvider = new StreamProvider(new FileInputStream(aClass));

        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, classProvider).getResult().get();
        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("foo.bar.BinaryExpr.Operator.AND") && n.getRange().get().begin.line == 7);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("AND", fae.get().resolve().getName());
    }
}
