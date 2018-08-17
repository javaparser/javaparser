package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class EnumLiteralsInAnnidatedClassTest {

    @Test
    public void resolveFieldOfEnumAsInternalClassOfClassUnqualifiedSamePackage() throws FileNotFoundException {
        File src = new File("src/test/resources/enumLiteralsInAnnidatedClass");
        File aClass = new File(src.getPath() + File.separator + "foo" + File.separator+ "bar"
                + File.separator + "AClass.java");

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(src));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser.setStaticConfiguration(parserConfiguration);

        CompilationUnit cu = JavaParser.parse(aClass);
        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("BinaryExpr.Operator.OR") && n.getRange().get().begin.line == 4);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("OR", fae.get().resolve().getName());
    }

    @Test
    public void resolveFieldOfEnumAsInternalClassOfClassQualifiedSamePackage() throws FileNotFoundException {
        File src = new File("src/test/resources/enumLiteralsInAnnidatedClass");
        File aClass = new File(src.getPath() + File.separator + "foo" + File.separator+ "bar"
                + File.separator + "AClass.java");

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(src));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser.setStaticConfiguration(parserConfiguration);

        CompilationUnit cu = JavaParser.parse(aClass);
        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("foo.bar.BinaryExpr.Operator.AND") && n.getRange().get().begin.line == 5);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("AND", fae.get().resolve().getName());
    }

    @Test
    public void resolveFieldOfEnumAsInternalClassOfClassUnqualifiedDifferentPackage() throws FileNotFoundException {
        File src = new File("src/test/resources/enumLiteralsInAnnidatedClass");
        File aClass = new File(src.getPath() + File.separator + "foo" + File.separator+ "bar"
                + File.separator + "differentpackage" + File.separator + "AClass2.java");

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(src));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser.setStaticConfiguration(parserConfiguration);

        CompilationUnit cu = JavaParser.parse(aClass);
        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("BinaryExpr.Operator.OR") && n.getRange().get().begin.line == 6);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("OR", fae.get().resolve().getName());
    }

    @Test
    public void resolveFieldOfEnumAsInternalClassOfClassQualifiedDifferentPackage() throws FileNotFoundException {
        File src = new File("src/test/resources/enumLiteralsInAnnidatedClass");
        File aClass = new File(src.getPath() + File.separator + "foo" + File.separator+ "bar"
                + File.separator + "differentpackage" + File.separator + "AClass2.java");

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(src));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser.setStaticConfiguration(parserConfiguration);

        CompilationUnit cu = JavaParser.parse(aClass);

        Optional<FieldAccessExpr> fae = cu.findFirst(FieldAccessExpr.class, n -> n.toString().equals("foo.bar.BinaryExpr.Operator.AND") && n.getRange().get().begin.line == 7);

        assertTrue(fae.isPresent());

        assertEquals("foo.bar.BinaryExpr.Operator", fae.get().resolve().getType().describe());
        assertEquals("AND", fae.get().resolve().getName());
    }
}
