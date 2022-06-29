package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.IOException;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ParserConfiguration.LanguageLevel;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2259Test extends AbstractResolutionTest {

    @BeforeEach
    void setup() {
    }
    
    @Test
    void test() throws IOException {
        // Source code
        String src = "public class TestClass2 {\n" + 
                "    public static void foo(Object o) {\n" + 
                "    }\n" + 
                "    public static void main(String[] args) {\n" + 
                "        foo(new Object[5]);\n" + 
                "    }\n" + 
                "}";
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver());

        // Setup symbol solver
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(typeSolver)).setLanguageLevel(LanguageLevel.JAVA_8);
        // Setup parser
        StaticJavaParser.setConfiguration(configuration);
        CompilationUnit cu = StaticJavaParser.parse(src);
        MethodCallExpr mce = cu.findFirst(MethodCallExpr.class).get();
        assertEquals("foo(new Object[5])",mce.toString());
        assertEquals("TestClass2.foo(java.lang.Object)",mce.resolve().getQualifiedSignature());
        assertEquals("void",mce.calculateResolvedType().describe());

    }

}
