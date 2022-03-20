package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class Issue2360 extends AbstractSymbolResolutionTest {

    @Test
    void testUnaryExprResolvedViaUnaryNumericPromotion_char() {
        String source = "public class Test\n" + 
                "{\n" + 
                "   public class InnerClass\n" + 
                "   {\n" + 
                "       public InnerClass(char c) {}\n" + 
                "       public InnerClass(int i) {}\n" + 
                "   }\n" + 
                "    \n" + 
                "   public Test() {\n" + 
                "     new InnerClass(+'.'); \n" + 
                "   }\n" + 
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(source);
        ObjectCreationExpr expr = cu.findFirst(ObjectCreationExpr.class).get();
        ResolvedConstructorDeclaration rcd = expr.resolve();
        assertEquals("InnerClass(int)", rcd.getSignature());
    }
    
    @Test
    void testUnaryExprResolvedViaUnaryNumericPromotion_byte() {
        String source = "public class Test\n" + 
                "{\n" + 
                "   public class InnerClass\n" + 
                "   {\n" + 
                "       public InnerClass(char c) {}\n" + 
                "       public InnerClass(int i) {}\n" + 
                "   }\n" + 
                "    \n" + 
                "   public Test() {\n" + 
                "     byte b = 0;\n" +
                "     new InnerClass(+b); \n" + 
                "   }\n" + 
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(source);
        ObjectCreationExpr expr = cu.findFirst(ObjectCreationExpr.class).get();
        ResolvedConstructorDeclaration rcd = expr.resolve();
        assertEquals("InnerClass(int)", rcd.getSignature());
    }
    
    @Test
    void testUnaryExprResolvedViaUnaryNumericPromotion_short() {
        String source = "public class Test\n" + 
                "{\n" + 
                "   public class InnerClass\n" + 
                "   {\n" + 
                "       public InnerClass(char c) {}\n" + 
                "       public InnerClass(int i) {}\n" + 
                "   }\n" + 
                "    \n" + 
                "   public Test() {\n" + 
                "     short b = 0;\n" +
                "     new InnerClass(+b); \n" + 
                "   }\n" + 
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(source);
        ObjectCreationExpr expr = cu.findFirst(ObjectCreationExpr.class).get();
        ResolvedConstructorDeclaration rcd = expr.resolve();
        assertEquals("InnerClass(int)", rcd.getSignature());
    }
    
}
