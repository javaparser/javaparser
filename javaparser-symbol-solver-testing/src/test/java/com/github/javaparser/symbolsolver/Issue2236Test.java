package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2236Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {
        final Path testRoot = adaptPath("src/test/resources/issue2236");
        TypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(testRoot);
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(reflectionTypeSolver, javaParserTypeSolver);
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(combinedTypeSolver));
        StaticJavaParser.setConfiguration(configuration);

        String src = "class X {public void f(){ " + 
                "new A<Object>(new Boolean(true)); }}";

        CompilationUnit cu = StaticJavaParser.parse(src);

        List<ObjectCreationExpr> oces = cu.findAll(ObjectCreationExpr .class);
        assertEquals("A.A(java.lang.Boolean)", oces.get(0).resolve().getQualifiedSignature());
        
    }
}
