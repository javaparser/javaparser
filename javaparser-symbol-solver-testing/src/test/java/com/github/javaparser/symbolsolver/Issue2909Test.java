package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
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
    
    @Test
    void testInDepth() {
        Path rootSourceDir = adaptPath("src/test/resources/issue2909");
        
        ParserConfiguration config = new ParserConfiguration();
        CombinedTypeSolver cts = new CombinedTypeSolver(new ReflectionTypeSolver(false), new JavaParserTypeSolver(rootSourceDir.toFile()));
        config.setSymbolResolver(new JavaSymbolSolver(cts));
        StaticJavaParser.setConfiguration(config);

        String s = "package test;\n" +
                "\n" +
                "public class Program {\n" +
//                "\n" +
//                "    public class OuterClass {\n" +
//                "    }\n" +
                "\n" +
                "    public class FarOuterClass {\n" +
                "\n" +
                "        public class OuterClass {\n" +
                "            int field = 0;\n" +
                "\n" +
                "            public class InnerClass {\n" +
                "                InnerClass() {\n" +
                "                    // Different cases to refer to enclosing type\n" +
                "                    OuterClass outer1 = OuterClass.this; // case1\n" +
                "                    OuterClass.this.field = 1; // case1\n" +
                "                    OuterClass outer2 = FarOuterClass.OuterClass.this; // case2\n" +
                "                    FarOuterClass.OuterClass.this.field = 1; // case2\n" +
                "                    OuterClass outer3 = Program.FarOuterClass.OuterClass.this; // case3\n" +
                "                    Program.FarOuterClass.OuterClass.this.field = 1; // case3\n" +
                "                    OuterClass outer4 = test.Program.FarOuterClass.OuterClass.this; // case4\n" +
                "                    test.Program.FarOuterClass.OuterClass.this.field = 1; // case4\n" +
                "                }\n" +
                "            }\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public class OuterClass {\n" +
                "    }\n" +
                "}";
        
        CompilationUnit cu = StaticJavaParser.parse(s);
        List<ThisExpr> exprs = cu.findAll(ThisExpr.class);
        exprs.forEach(expr-> {
            System.out.println(String.format("%s is resolved to %s", expr.toString(), expr.calculateResolvedType().describe()));
            assertEquals("test.Program.FarOuterClass.OuterClass",expr.calculateResolvedType().describe());
        });
    }
}
