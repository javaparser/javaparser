package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;


public class Issue1868Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {
        
        Path testResources= adaptPath("src/test/resources/issue1868");
        
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(testResources));

        StaticJavaParser.setConfiguration(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)));

        String s = 
                "class A {\n" + 
                "    public void foo() {\n" + 
                "        toArray(new String[0]);\n" + 
                "    }\n" + 
                "    public void bar() {\n" + 
                "        B b = null;\n" + 
                "        b.toArray(new String[0]);\n" + 
                "    }\n" + 
                "    public <T> T[] toArray(T[] tArray) {\n" + 
                "        // ...\n" + 
                "    }\n" + 
                "}";
        
        CompilationUnit cu = StaticJavaParser.parse(s);
        
        List<MethodCallExpr> mces = cu.findAll(MethodCallExpr.class);
        
        assertEquals("toArray(new String[0]) resolved to A.toArray",String.format("%s resolved to %s", mces.get(0), mces.get(0).resolve().getQualifiedName()));
        assertEquals("b.toArray(new String[0]) resolved to B.toArray",String.format("%s resolved to %s", mces.get(1), mces.get(1).resolve().getQualifiedName()));
        
    }

}
