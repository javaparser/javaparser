package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

public class Issue2481Test {

    @Test
    public void test() {
        TypeSolver solver = new ReflectionTypeSolver();
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(solver));
        JavaParser parser = new JavaParser(parserConfiguration);
        ParseResult<CompilationUnit> cu = parser.parse("class A<T> { T t; }");
        cu.ifSuccessful( c -> {
            c.accept(new VoidVisitorAdapter<Void>() {
                @Override
                public void visit(ClassOrInterfaceType n, Void arg) {
                    super.visit(n, arg);
                    n.resolve();
                }
            }, null);
        });
    }

}
