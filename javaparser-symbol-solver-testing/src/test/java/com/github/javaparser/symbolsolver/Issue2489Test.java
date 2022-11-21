package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2489Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {
        final Path testRoot = adaptPath("src/test/resources/issue2489");
        TypeSolver reflectionTypeSolver = new ReflectionTypeSolver(false);
        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(testRoot);
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(reflectionTypeSolver, javaParserTypeSolver);
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(combinedTypeSolver));
        StaticJavaParser.setConfiguration(configuration);

        String src = "public class B {\n" +
                "  public void m() {\n" +
                "    ComponentBase otm4e = new ComponentBase();\n" +
                "    otm4e.set(\"OTM4E_EFFLEVEL\", \"IE1 / STD\", true);\n" +
                "  }\n" +
                "\n" +
                "}";

        CompilationUnit cu = StaticJavaParser.parse(src);

        List<MethodCallExpr> mces = cu.findAll(MethodCallExpr.class);
        assertEquals("ObjectContext.set(java.lang.String, java.lang.Object, boolean)", mces.get(0).resolve().getQualifiedSignature());
    }

}
