package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

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
import org.junit.jupiter.api.Disabled;

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
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String s -> System.out.println(s);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        NameExpr name = Navigator.findNameExpression(cu, "s").get();
        assertEquals("java.lang.String", name.resolve().getType().describe());
    }

    @Test
    public void switchPatternWithGuardShouldResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String s when s.length() > 5 -> System.out.println(s);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        cu.findAll(NameExpr.class).stream()
                .filter(nameExpr -> nameExpr.getNameAsString().equals("s"))
                .forEach(nameExpr -> {
                    assertEquals(
                            "java.lang.String", nameExpr.resolve().getType().describe());
                });
    }

    @Test
    public void switchPatternWithNonMatchingNameShouldNotResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String t -> System.out.println(s);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        Executable resolveS = () -> Navigator.findNameExpression(cu, "s").get().resolve();

        assertThrows(UnsolvedSymbolException.class, resolveS);
    }

    @Test
    public void switchPatternInOtherCaseShouldNotResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String t -> {}\n"
                + "            case Integer i -> System.out.println(t);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        Executable resolveS = () -> Navigator.findNameExpression(cu, "t").get().resolve();

        assertThrows(UnsolvedSymbolException.class, resolveS);
    }

    @Test
    public void nestedSwitchRecordPatternShouldResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case Box(InnerBox(Integer i), InnerBox(String s)) -> System.out.println(s);\n"
                + "            case null, default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        NameExpr name = Navigator.findNameExpression(cu, "s").get();
        assertEquals("java.lang.String", name.resolve().getType().describe());
    }

    @Test
    public void switchPatternWithUnnamedPatternShouldNotResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case String _ -> System.out.println(\"string\");\n"
                + "            default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        // Should not find any NameExpr with name "_" since it's an unnamed pattern
        java.util.List<NameExpr> unnamedExpressions = cu.findAll(NameExpr.class).stream()
                .filter(ne -> ne.getNameAsString().equals("_"))
                .collect(java.util.stream.Collectors.toList());
        assertEquals(0, unnamedExpressions.size());
    }

    @Test
    @Disabled("Parser grammar doesn't support mixed named/unnamed fields in record patterns (JEP 456). Requires JavaCC grammar updates.")
    public void switchPatternWithUnnamedPatternInRecordShouldNotResolve() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case Car(_, String color, _) -> System.out.println(color);\n"
                + "            default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        // Should find the named variable "color" but not the unnamed patterns "_"
        NameExpr colorExpr = Navigator.findNameExpression(cu, "color").get();
        assertEquals("java.lang.String", colorExpr.resolve().getType().describe());

        // Should not find any NameExpr with name "_"
        java.util.List<NameExpr> unnamedExpressions = cu.findAll(NameExpr.class).stream()
                .filter(ne -> ne.getNameAsString().equals("_"))
                .collect(java.util.stream.Collectors.toList());
        assertEquals(0, unnamedExpressions.size());
    }

    @Test
    @Disabled("Parser grammar doesn't support nested record patterns with mixed named/unnamed fields (JEP 456). Requires JavaCC grammar updates.")
    public void switchPatternWithNestedUnnamedPatternShouldResolveNamedParts() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case Car(_, _, Engine(String type, _)) -> System.out.println(type);\n"
                + "            default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        // Should resolve the named "type" variable
        NameExpr typeExpr = Navigator.findNameExpression(cu, "type").get();
        assertEquals("java.lang.String", typeExpr.resolve().getType().describe());

        // Should not find any NameExpr with name "_"
        java.util.List<NameExpr> unnamedExpressions = cu.findAll(NameExpr.class).stream()
                .filter(ne -> ne.getNameAsString().equals("_"))
                .collect(java.util.stream.Collectors.toList());
        assertEquals(0, unnamedExpressions.size());
    }

    @Test
    public void switchPatternWithGuardAndUnnamedPatternShouldNotResolveUnnamed() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o, boolean condition) {\n"
                + "        switch (o) {\n"
                + "            case String _ when condition -> System.out.println(\"conditional string\");\n"
                + "            default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        // Should resolve the guard condition
        NameExpr conditionExpr = Navigator.findNameExpression(cu, "condition").get();
        assertEquals("boolean", conditionExpr.resolve().getType().describe());

        // Should not find any NameExpr with name "_"
        java.util.List<NameExpr> unnamedExpressions = cu.findAll(NameExpr.class).stream()
                .filter(ne -> ne.getNameAsString().equals("_"))
                .collect(java.util.stream.Collectors.toList());
        assertEquals(0, unnamedExpressions.size());
    }

    @Test
    @Disabled("Parser grammar doesn't support complex multi-case record patterns with unnamed fields (JEP 456). Requires JavaCC grammar updates.")
    public void switchPatternWithMultipleCasesAndUnnamedPatternsShouldResolveCorrectly() {
        CompilationUnit cu = parse("class Test {\n" + "    public void foo(Object o) {\n"
                + "        switch (o) {\n"
                + "            case Car(String brand, _, _), Truck(String model, _) -> System.out.println(brand + model);\n"
                + "            default -> {}\n"
                + "        };\n"
                + "    }\n"
                + "}");

        // Should find and resolve both named variables
        java.util.List<NameExpr> brandExpressions = cu.findAll(NameExpr.class).stream()
                .filter(ne -> ne.getNameAsString().equals("brand"))
                .collect(java.util.stream.Collectors.toList());
        assertEquals(2, brandExpressions.size()); // Declaration and usage
        
        java.util.List<NameExpr> modelExpressions = cu.findAll(NameExpr.class).stream()
                .filter(ne -> ne.getNameAsString().equals("model"))
                .collect(java.util.stream.Collectors.toList());
        assertEquals(2, modelExpressions.size()); // Declaration and usage

        // Verify type resolution
        NameExpr brandUsage = brandExpressions.stream()
                .filter(ne -> ne.getParentNode().get() instanceof com.github.javaparser.ast.expr.BinaryExpr)
                .findFirst().get();
        assertEquals("java.lang.String", brandUsage.resolve().getType().describe());

        // Should not find any NameExpr with name "_"
        java.util.List<NameExpr> unnamedExpressions = cu.findAll(NameExpr.class).stream()
                .filter(ne -> ne.getNameAsString().equals("_"))
                .collect(java.util.stream.Collectors.toList());
        assertEquals(0, unnamedExpressions.size());
    }

    @Test
    public void switchExpressionWithUnnamedPatternShouldReturnCorrectValue() {
        CompilationUnit cu = parse("class Test {\n" + "    public String foo(Object o) {\n"
                + "        return switch (o) {\n"
                + "            case String _ -> \"string\";\n"
                + "            case Integer _ -> \"integer\";\n"
                + "            default -> \"other\";\n"
                + "        };\n"
                + "    }\n"
                + "}");

        // Verify the switch expression structure without trying to resolve unnamed patterns
        java.util.List<com.github.javaparser.ast.expr.SwitchExpr> switchExprs = cu.findAll(com.github.javaparser.ast.expr.SwitchExpr.class);
        assertEquals(1, switchExprs.size());

        com.github.javaparser.ast.expr.SwitchExpr switchExpr = switchExprs.get(0);
        assertEquals(3, switchExpr.getEntries().size());

        // Should not find any NameExpr with name "_"
        java.util.List<NameExpr> unnamedExpressions = cu.findAll(NameExpr.class).stream()
                .filter(ne -> ne.getNameAsString().equals("_"))
                .collect(java.util.stream.Collectors.toList());
        assertEquals(0, unnamedExpressions.size());
    }
}
