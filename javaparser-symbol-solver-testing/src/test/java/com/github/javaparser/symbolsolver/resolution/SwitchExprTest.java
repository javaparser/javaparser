package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public class SwitchExprTest {
    private CompilationUnit parse(String code) {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
        return new JavaParser(parserConfiguration).parse(code).getResult().get();
    }

    @Test
    public void switchPatternShouldResolve() {
        CompilationUnit cu = parse("class Test {\n" +
                "    public void foo(Object o) {\n" +
                "        switch (o) {\n" +
                "            case String s -> System.out.println(s);\n" +
                "            case null, default -> {}\n" +
                "        };\n" +
                "    }\n" +
                "}"
        );

        NameExpr name = Navigator.findNameExpression(cu, "s").get();
        assertEquals("java.lang.String", name.resolve().getType().describe());
    }

    @Test
    public void switchPatternWithGuardShouldResolve() {
        CompilationUnit cu = parse("class Test {\n" +
                "    public void foo(Object o) {\n" +
                "        switch (o) {\n" +
                "            case String s when s.length() > 5 -> System.out.println(s);\n" +
                "            case null, default -> {}\n" +
                "        };\n" +
                "    }\n" +
                "}"
        );

        cu.findAll(NameExpr.class).stream().filter(nameExpr -> nameExpr.getNameAsString().equals("s")).forEach(nameExpr -> {
            assertEquals("java.lang.String", nameExpr.resolve().getType().describe());
        });
    }

    @Test
    public void switchPatternWithNonMatchingNameShouldNotResolve() {
        CompilationUnit cu = parse("class Test {\n" +
                "    public void foo(Object o) {\n" +
                "        switch (o) {\n" +
                "            case String t -> System.out.println(s);\n" +
                "            case null, default -> {}\n" +
                "        };\n" +
                "    }\n" +
                "}"
        );

        Executable resolveS = () -> Navigator.findNameExpression(cu, "s").get().resolve();

        assertThrows(UnsolvedSymbolException.class, resolveS);
    }

    @Test
    public void switchPatternInOtherCaseShouldNotResolve() {
        CompilationUnit cu = parse("class Test {\n" +
                "    public void foo(Object o) {\n" +
                "        switch (o) {\n" +
                "            case String t -> {}\n" +
                "            case Integer i -> System.out.println(t);\n" +
                "            case null, default -> {}\n" +
                "        };\n" +
                "    }\n" +
                "}"
        );

        Executable resolveS = () -> Navigator.findNameExpression(cu, "t").get().resolve();

        assertThrows(UnsolvedSymbolException.class, resolveS);
    }

    @Test
    public void nestedSwitchRecordPatternShouldResolve() {
        CompilationUnit cu = parse("class Test {\n" +
                "    public void foo(Object o) {\n" +
                "        switch (o) {\n" +
                "            case Box(InnerBox(Integer i), InnerBox(String s)) -> System.out.println(s);\n" +
                "            case null, default -> {}\n" +
                "        };\n" +
                "    }\n" +
                "}"
        );

        NameExpr name = Navigator.findNameExpression(cu, "s").get();
        assertEquals("java.lang.String", name.resolve().getType().describe());
    }
}
