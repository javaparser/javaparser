package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2909Test extends AbstractResolutionTest {

    @Test
    void testResolvingLocallyFromCompleteReferenceToInnerClass() {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        String s = 
                "public class Program {\n" + 
                "\n" + 
                "    public class OuterClass {\n" + 
                "        int field = 0;\n" + 
                "\n" + 
                "        public class InnerClass {\n" + 
                "            InnerClass() {\n" + 
                "               OuterClass outer = Program.OuterClass.this;\n" + 
                "               Program.OuterClass.this.field = 1;\n" + 
                "            }\n" + 
                "        }\n" + 
                "    }\n" + 
                "}";
        
        CompilationUnit cu = StaticJavaParser.parse(s);
        List<ThisExpr> exprs = cu.findAll(ThisExpr.class);
        exprs.forEach(expr-> {
            assertEquals("Program.OuterClass",expr.calculateResolvedType().describe());
        });
    }
    
    @Test
    void testResolvingLocallyFromPartialReferenceToInnerClass() {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        String s = 
                "public class Program {\n" +
                        "\n" +
                        "    public class OuterClass {\n" +
                        "        int field = 0;\n" +
                        "\n" +
                        "        public class InnerClass {\n" +
                        "            InnerClass() {\n" +
                        "               OuterClass outer = OuterClass.this;\n" +
                        "               OuterClass.this.field = 1;\n" +
                        "            }\n" +
                        "        }\n" +
                        "    }\n" +
                        "}";
        
        CompilationUnit cu = StaticJavaParser.parse(s);
        List<ThisExpr> exprs = cu.findAll(ThisExpr.class);
        exprs.forEach(expr-> {
            assertEquals("Program.OuterClass",expr.calculateResolvedType().describe());
        });
    }
}
