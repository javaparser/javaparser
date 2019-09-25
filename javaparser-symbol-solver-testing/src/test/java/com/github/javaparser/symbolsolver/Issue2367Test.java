package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.StreamProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;

class Issue2367Test extends AbstractSymbolResolutionTest {

    @Test
    void issue2367() throws IOException {
        Path dir = adaptPath("src/test/resources/issue2367");
        Path file = adaptPath("src/test/resources/issue2367/Issue2367.java");

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JavaParserTypeSolver(dir));

        JavaParser javaParser = new JavaParser();
        javaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();

        NameExpr nameExpr = unit.findFirst(NameExpr.class, m -> m.getName().getIdentifier().equals("privateField")).get();
        ResolvedValueDeclaration resolvedValueDeclaration = nameExpr.resolve();
        assertEquals("double", resolvedValueDeclaration.getType().describe());
    }
}