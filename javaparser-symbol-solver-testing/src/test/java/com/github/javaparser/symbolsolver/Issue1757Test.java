package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue1757Test extends AbstractResolutionTest {

    @Test()
    void test() throws IOException {
        
        String src =
                "import java.util.Comparator;\n" + 
                "public class A {\n" + 
                "    public void m() {\n" + 
                "        Comparator<String> c = new Comparator<String>() {\n" + 
                "            public int compare(String o1, String o2) {\n" + 
                "                return 0;\n" + 
                "            }\n" + 
                "        };\n" + 
                "    }\n" + 
                "}";

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(src);
        
        ObjectCreationExpr oce = cu.findFirst(ObjectCreationExpr.class).get();
        assertEquals("java.util.Comparator<java.lang.String>", oce.calculateResolvedType().describe());
        assertTrue(oce.resolve().getQualifiedName().startsWith("A.Anonymous"));
    }
    
}
