package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2909Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {
        
        TypeSolver typeSolver = new ReflectionTypeSolver(false);
        ParserConfiguration config = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(typeSolver));
        StaticJavaParser.setConfiguration(config);

        String code = 
                "public class Program {\n" + 
                "\n" + 
                "    public class OuterClass {\n" + 
                "        int field = 0;\n" + 
                "\n" + 
                "        public class InnerClass {\n" + 
                "            InnerClass() {\n" + 
                "               OuterClass outer = Program.OuterClass.this;\n" + 
                "                Program.OuterClass.this.field = 1;\n" + 
                "            }\n" + 
                "        }\n" + 
                "    }\n" + 
                "}";
        CompilationUnit cu = StaticJavaParser.parse(code);
        cu.findAll(ThisExpr.class).forEach(t -> {
            assertEquals("Program.OuterClass",t.calculateResolvedType().describe());
        });
        
    }
    
    public enum A {
        public enum B {
            
        }
    }
    
}
