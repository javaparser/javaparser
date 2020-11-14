package com.github.javaparser.symbolsolver;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2823Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {
        final Path testRoot = adaptPath("src/test/resources/issue2823");
        TypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(testRoot);
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(reflectionTypeSolver, javaParserTypeSolver);
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(combinedTypeSolver));
        StaticJavaParser.setConfiguration(configuration);

        String src = "import java.util.Optional;\n"
                + "public class TestClass {\n"
                + "    public Long getValue() {\n"
                + "        Optional<ClassA> classA = Optional.of(new ClassA());\n"
                + "        return classA.map(a -> a.obj)\n"
                + "                .map(b -> b.value)\n"
                + "                .orElse(null);\n"
                + "    }\n"
                + "}";

        CompilationUnit cu = StaticJavaParser.parse(src);

        // verify there is no exception thrown when we try to resolve all field access expressions
        cu.findAll(FieldAccessExpr.class).forEach(fd -> fd.resolve());

    }
}
