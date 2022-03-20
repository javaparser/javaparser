package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue3028Test extends AbstractResolutionTest {

    @Test
    void varArgsIssue() {
    	
    	TypeSolver typeSolver = new CombinedTypeSolver(
				new ReflectionTypeSolver());
		JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
		
		StaticJavaParser.getConfiguration().setSymbolResolver(symbolSolver);
		
        CompilationUnit cu = parseSample("Issue3028");
        
        final MethodCallExpr mce = Navigator.findMethodCall(cu, "doSomething").get();
        ResolvedMethodDeclaration rmd = mce.resolve();
        assertEquals("AParserTest.doSomething(java.lang.String, java.util.function.Supplier<?>...)", rmd.getQualifiedSignature());
        
    }
    
}
