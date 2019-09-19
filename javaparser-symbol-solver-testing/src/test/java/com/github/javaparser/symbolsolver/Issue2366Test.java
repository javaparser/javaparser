package com.github.javaparser.symbolsolver;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ParserConfiguration.LanguageLevel;
import com.github.javaparser.StreamProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class Issue2366Test extends AbstractSymbolResolutionTest {
	
    @Test()
    void testInvalidArgumentNumber() throws IOException {
        Path file = adaptPath("src/test/resources/issue2366/Test.java");

        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(new ReflectionTypeSolver());	    

        ParserConfiguration pc = new ParserConfiguration()
            	                        .setSymbolResolver(new JavaSymbolSolver(combinedSolver))
            	                        .setLanguageLevel(LanguageLevel.JAVA_8);

        JavaParser javaParser = new JavaParser(pc);

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();
        
        Assertions.assertThrows(UnsolvedSymbolException.class, () -> unit.accept(new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(ObjectCreationExpr exp, Object arg) {
                exp.resolve().getSignature();
            }            
        }, null));
    }
    
    @Test()
    void compareFindAllSizeWithVoidVisitorAdapterSize() throws IOException {
        Path file = adaptPath("src/test/resources/issue2366/Test2.java");

        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(new ReflectionTypeSolver());	    

        ParserConfiguration pc = new ParserConfiguration()
            	                        .setSymbolResolver(new JavaSymbolSolver(combinedSolver))
            	                        .setLanguageLevel(LanguageLevel.JAVA_8);

        JavaParser javaParser = new JavaParser(pc);

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();
        
        List<ObjectCreationExpr> oce = unit.findAll(ObjectCreationExpr.class);
        
        AtomicInteger foundObjs = new AtomicInteger(0);
		unit.accept(new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(ObjectCreationExpr exp, Object arg) {
            	super.visit(exp, arg);
                ((AtomicInteger)arg).incrementAndGet();
            }            
        }, foundObjs);
        
		Assertions.assertEquals(oce.size(), foundObjs.get());
    }
    
    @Test()
    void testFindAllSize() throws IOException {
        Path file = adaptPath("src/test/resources/issue2366/Test2.java");

        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(new ReflectionTypeSolver());	    

        ParserConfiguration pc = new ParserConfiguration()
            	                        .setSymbolResolver(new JavaSymbolSolver(combinedSolver))
            	                        .setLanguageLevel(LanguageLevel.JAVA_8);

        JavaParser javaParser = new JavaParser(pc);

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();
        
        List<ObjectCreationExpr> oce = unit.findAll(ObjectCreationExpr.class);
        
        Assertions.assertEquals(2, oce.size());
    }
}