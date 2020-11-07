package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;


public class Issue2132Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {
        
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        StaticJavaParser.setConfiguration(config);

        String s = 
                "class A {\n" + 
                "    void method() {\n" + 
                "        String s = \"\";\n" + 
                "        {\n" + 
                "          s.length();\n" + 
                "        }\n" + 
                "    }\n" + 
                "}";
        CompilationUnit cu = StaticJavaParser.parse(s);
        MethodCallExpr mce = cu.findFirst(MethodCallExpr.class).get();
        assertEquals("int", mce.calculateResolvedType().describe());
        assertEquals("java.lang.String.length", mce.resolve().getQualifiedName());
        assertEquals("java.lang.String", mce.getScope().get().calculateResolvedType().describe());
    }

}
