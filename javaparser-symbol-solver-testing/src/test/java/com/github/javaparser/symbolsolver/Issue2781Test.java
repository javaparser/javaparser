package com.github.javaparser.symbolsolver;

import java.io.FileNotFoundException;
import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2781Test extends AbstractResolutionTest {
    
    @Test()
    void test() throws FileNotFoundException {
        
        String code =
                "public class A implements AnInterface {\n" + 
                "        private AnInterface field;\n" + 
                "\n" + 
                "        protected AnInterface getContainer() {\n" + 
                "            return this.field;\n" + 
                "        }\n" + 
                "        protected static class AnInterface {\n" + 
                "        }\n" + 
                "}";
        
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath("src/test/resources")));
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(combinedTypeSolver));
        
        CompilationUnit cu = StaticJavaParser.parse(code);
        List<ConstructorDeclaration> constructorDeclarations = cu.findAll(ConstructorDeclaration.class);
        constructorDeclarations.forEach(constructorDeclaration -> {
            constructorDeclaration.findAll(MethodCallExpr.class).forEach(methodCallExpr -> {
                //Exception in thread "main" java.lang.StackOverflowError
                ResolvedMethodDeclaration rmd = methodCallExpr.resolve();
                System.out.println(rmd.getQualifiedName());
            });
        });

        
    }
    
}
