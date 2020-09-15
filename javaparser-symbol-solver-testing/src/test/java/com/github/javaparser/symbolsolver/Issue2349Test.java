package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.List;

import org.junit.jupiter.api.BeforeEach;

public class Issue2349Test extends AbstractResolutionTest {

    @BeforeEach
    void setUp() {
        CombinedTypeSolver cts = new CombinedTypeSolver(new ReflectionTypeSolver(),
                new JavaParserTypeSolver("src/test/resources/issue2349"));
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(cts));
        StaticJavaParser.setConfiguration(config);
    }

    @Test
    void test() throws FileNotFoundException {
        CompilationUnit cu = parse(new File("src/test/resources/issue2349/foo/Bar.java"));
        List<ClassOrInterfaceDeclaration> decls = cu.findAll(ClassOrInterfaceDeclaration.class);
        ResolvedReferenceType rrt = decls.get(0).getExtendedTypes().getFirst().get().resolve();
        assertTrue("bar.Bar".equals(rrt.describe()));
    }

}
