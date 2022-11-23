package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2995Test extends AbstractResolutionTest {

    @Test
    public void test() {
        ParserConfiguration config = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        String str = "public class MyClass {\n" +
                "   class Inner1 {\n" +
                "       class Inner2 {\n" +
                "       }\n" +
                "   }\n" +
                "   {\n" +
                "       new Inner1().new Inner2();\n" +
                "   }\n" +
                "}\n";
        CompilationUnit cu = StaticJavaParser.parse(str);
        List<ObjectCreationExpr> exprs = cu.findAll(ObjectCreationExpr.class);
        assertEquals("new Inner1().new Inner2()", exprs.get(0).toString());
        assertEquals("MyClass.Inner1.Inner2", exprs.get(0).getType().resolve().describe());
        assertEquals("new Inner1()", exprs.get(1).toString());
        assertEquals("MyClass.Inner1", exprs.get(1).getType().resolve().describe());
    }
}
