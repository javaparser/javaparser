package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

public class Issue3308Test {

    @Test
    void test() {
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
//        List<ArrayAccessExpr> all = node.findAll(ArrayAccessExpr.class);
//        List<NameExpr> all = node.findAll(NameExpr.class);
        List<FieldAccessExpr> all = node.findAll(FieldAccessExpr.class);
        all.remove(0);
        all.forEach(a -> {
            System.out.println("a = " + a);
            System.out.println("a.getName() = " + a.getName());
            try {
                ResolvedValueDeclaration resolved = a.resolve();
                System.out.println("resolved = " + resolved);
            } catch (Exception e) {
                System.out.println("e = " + e);
            }
            System.out.println();
        });
    }




    @Test
    void test2() {
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
        List<ArrayAccessExpr> all = node.findAll(ArrayAccessExpr.class);
//        List<NameExpr> all = node.findAll(NameExpr.class);
//        List<FieldAccessExpr> all = node.findAll(FieldAccessExpr.class);
        all.remove(0);
        all.forEach(a -> {
            System.out.println("a = " + a);
            System.out.println("a.getName() = " + a.getName());
//            try {
//                ResolvedValueDeclaration resolved = a.resolve();
//                System.out.println("resolved = " + resolved);
//            } catch (Exception e) {
//                System.out.println("e = " + e);
//            }
            System.out.println();
        });
    }

}
