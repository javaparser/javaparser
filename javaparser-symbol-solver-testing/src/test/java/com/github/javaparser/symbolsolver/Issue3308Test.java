package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue3308Test {

    @Test
    void shallowArray() {
        StaticJavaParser.getConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_9);
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(combinedTypeSolver));
        String classStr = "public class JavaParser {\n" +
                "\n" +
                "    public void bad (int index) {\n" +
                "        LastRecovered recovered = new LastRecovered();\n" +
                "        recovered.perPriority[index].recovered = 10;\n" +
                "    }\n" +
                "\n" +
                "    private class LastRecovered {\n" +
                "        LastRecoveredEntry[] perPriority = new LastRecoveredEntry[10];\n" +
                "    }\n" +
                "\n" +
                "    private class LastRecoveredEntry {\n" +
                "        private int recovered = 0;\n" +
                "    }\n" +
                "}";

        CompilationUnit node = StaticJavaParser.parse(classStr);
        List<FieldAccessExpr> all = node.findAll(FieldAccessExpr.class);
        assertEquals(2, all.size());

        ResolvedValueDeclaration resolved;
        FieldAccessExpr fieldAccessExpr;

        fieldAccessExpr = all.get(0);
        Assertions.assertEquals("recovered", fieldAccessExpr.getNameAsString());
        resolved = fieldAccessExpr.resolve();
        assertTrue(resolved.getType().isPrimitive());
        assertEquals("java.lang.Integer", resolved.getType().asPrimitive().getBoxTypeQName());


        fieldAccessExpr = all.get(1);
        Assertions.assertEquals("perPriority", fieldAccessExpr.getNameAsString());
        resolved = fieldAccessExpr.resolve();
        assertTrue(resolved.getType().isArray());
    }




    @Test
    void deepArray() {
        StaticJavaParser.getConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_9);
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(combinedTypeSolver));
        String classStr = "class JavaParser {\n" +
                "\n" +
                "    public void bad (int index) {\n" +
                "        LastRecovered recovered = new LastRecovered();\n" +
                "        recovered.perPriority[index][0][0][0].recovered = 10;\n" +
                "    }\n" +
                "\n" +
                "    private class LastRecovered {\n" +
                "        LastRecoveredEntry[][][][] perPriority = new LastRecoveredEntry[10][10][10][10];\n" +
                "    }\n" +
                "\n" +
                "    private class LastRecoveredEntry {\n" +
                "        private int recovered = 0;\n" +
                "    }\n" +
                "}";

        CompilationUnit node = StaticJavaParser.parse(classStr);
        List<FieldAccessExpr> all = node.findAll(FieldAccessExpr.class);
        assertEquals(2, all.size());

        ResolvedValueDeclaration resolved;
        FieldAccessExpr fieldAccessExpr;

        fieldAccessExpr = all.get(0);
        Assertions.assertEquals("recovered", fieldAccessExpr.getNameAsString());
        resolved = fieldAccessExpr.resolve();
        assertTrue(resolved.getType().isPrimitive());
        assertEquals("java.lang.Integer", resolved.getType().asPrimitive().getBoxTypeQName());


        fieldAccessExpr = all.get(1);
        Assertions.assertEquals("perPriority", fieldAccessExpr.getNameAsString());
        resolved = fieldAccessExpr.resolve();
        assertTrue(resolved.getType().isArray());

    }

}
