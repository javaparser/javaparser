package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2289Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {

        TypeSolver typeSolver = new ReflectionTypeSolver(false);
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        StaticJavaParser.setConfiguration(config);

        String s = 
                "public class Test \n" + 
                "{\n" + 
                "    public class InnerClass \n" + 
                "    {\n" + 
                "        public InnerClass(int i, int j) {  \n" + 
                "        }\n" + 
                "\n" + 
                "        public InnerClass(int i, int ...j) {  \n" + 
                "        } \n" + 
                "    }\n" + 
                " \n" + 
                "    public Test() { \n" + 
                "        new InnerClass(1,2);\n" + 
                "        new InnerClass(1,2,3);\n" + 
                "    } \n" + 
                "}";
        
        CompilationUnit cu = StaticJavaParser.parse(s);
        List<ObjectCreationExpr> exprs = cu.findAll(ObjectCreationExpr .class);
        
        assertEquals("Test.InnerClass.InnerClass(int, int)", exprs.get(0).resolve().getQualifiedSignature());
        assertEquals("Test.InnerClass.InnerClass(int, int...)", exprs.get(1).resolve().getQualifiedSignature());

    }
    
}
