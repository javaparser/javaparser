package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;


public class Issue1817Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {
        
        Path testResources= adaptPath("src/test/resources/issue1817");
        
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(testResources));

        StaticJavaParser.setConfiguration(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)));

        String s = 
                "interface A extends X.A {\n" + 
                "    default void foo() {\n" + 
                "        X.A xa = null;\n" + 
                "        xa.bar();\n" + 
                "    }\n" + 
                "}";
        
        CompilationUnit cu = StaticJavaParser.parse(s);
        
        MethodCallExpr mce = cu.findFirst(MethodCallExpr.class).get();
        
        assertEquals("X.A.bar",mce.resolve().getQualifiedName());
    }

}
