package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2062Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        String s = "import java.util.Optional;\n" +
                "public class Base{\n" +
                "    class Derived extends Base{\n" +
                "    }\n" +
                "    \n" +
                "    public void bar(Optional<Base> o) {\n" +
                "    }\n" +
                "    public void foo() {\n" +
                "        bar(Optional.of(new Derived()));\n" +
                "    }\n" +
                "}";
        CompilationUnit cu = StaticJavaParser.parse(s);
        List<MethodCallExpr> mces = cu.findAll(MethodCallExpr.class);
        assertEquals("bar(Optional.of(new Derived()))", mces.get(0).toString());
        assertEquals("Base.bar(java.util.Optional<Base>)", mces.get(0).resolve().getQualifiedSignature());

    }

}
