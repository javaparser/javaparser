package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import org.junit.jupiter.api.Test;

public class Issue4488Test {
    @Test
    void cannotChangeMethodNameInLambda() {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setLexicalPreservationEnabled(true);
        StaticJavaParser.setConfiguration(parserConfiguration);

        CompilationUnit cu =
                StaticJavaParser.parse("class Test {\n" + "	private Map<String, String> dummyMap = new HashMap<>();\n"
                        + "	public String dummyFunction(String name) {\n"
                        + "		return dummyMap.computeIfAbsent(name,\n"
                        + "			(Function<String, String>) s -> SomeFunction.withAMethodHere(\"test\").build());\n"
                        + "	}\n"
                        + "}");

        cu.accept(
                new ModifierVisitor() {
                    @Override
                    public Visitable visit(MethodCallExpr mc, Object arg) {
                        if (mc.getNameAsString().equals("withAMethodHere")) {
                            return mc.setName("replacedMethodHere");
                        }
                        return super.visit(mc, arg);
                    }
                },
                null);

        assertEquals(
                "class Test {\n" + "	private Map<String, String> dummyMap = new HashMap<>();\n"
                        + "	public String dummyFunction(String name) {\n"
                        + "		return dummyMap.computeIfAbsent(name,\n"
                        + "			(Function<String, String>) s -> SomeFunction.replacedMethodHere(\"test\").build());\n"
                        + "	}\n"
                        + "}",
                LexicalPreservingPrinter.print(cu));
    }
}
