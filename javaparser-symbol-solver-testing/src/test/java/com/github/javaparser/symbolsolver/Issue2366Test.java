package com.github.javaparser.symbolsolver;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

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
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class Issue2366Test extends AbstractSymbolResolutionTest {
	
    @Test()
    void issue2366() throws IOException {
        Path dir = adaptPath("src/test/resources/issue2366");
        Path file = adaptPath("src/test/resources/issue2366/Test.java");

        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(new ReflectionTypeSolver());	    

        ParserConfiguration pc = new ParserConfiguration()
            	                        .setSymbolResolver(new JavaSymbolSolver(combinedSolver))
            	                        .setLanguageLevel(LanguageLevel.JAVA_8);

        JavaParser javaParser = new JavaParser(pc);

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();
        
        ObjectCreationExpr oce = unit.findFirst(ObjectCreationExpr.class).get();
        

        Assertions.assertThrows(UnsolvedSymbolException.class, () -> unit.accept(new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(ObjectCreationExpr exp, Object arg) {
                exp.resolve().getSignature();
            }            
        }, null));
    }
    
    @Test()
    void issue2366_2() throws IOException {
        Path dir = adaptPath("src/test/resources/issue2366");
        Path file = adaptPath("src/test/resources/issue2366/Test2.java");

        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(new ReflectionTypeSolver());	    

        ParserConfiguration pc = new ParserConfiguration()
            	                        .setSymbolResolver(new JavaSymbolSolver(combinedSolver))
            	                        .setLanguageLevel(LanguageLevel.JAVA_8);

        JavaParser javaParser = new JavaParser(pc);

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();
        
        ObjectCreationExpr oce = unit.findFirst(ObjectCreationExpr.class).get();
        

        unit.accept(new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(ObjectCreationExpr exp, Object arg) {
                System.out.println(exp.resolve().getSignature());
            }            
        }, null);
    }
    
    @Test()
    void issue2370() throws IOException {
        Path dir = adaptPath("src/test/resources/issue2366");
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