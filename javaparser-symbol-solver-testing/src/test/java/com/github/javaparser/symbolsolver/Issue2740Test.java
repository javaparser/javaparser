package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

public class Issue2740Test extends AbstractResolutionTest {

    @Test()
    void test() {
        String code =
                "import java.util.function.Consumer;\n" + 
                "import java.util.ArrayList;\n" + 
                "\n" + 
                "public class A {\n" + 
                "    \n" + 
                "    void m() {\n" + 
                "        new Consumer<String>() {\n" + 
                "            private ArrayList<Integer> t = new ArrayList<>();\n" + 
                "            @Override\n" + 
                "            public void accept(String s) {\n" + 
                "                t.add(s);\n" + 
                "            }\n" + 
                "            \n" + 
                "        };" + 
                "    }\n" + 
                "\n" + 
                "}";

        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(code);
        List<MethodCallExpr> methodCallExpr = cu.findAll(MethodCallExpr.class);
        for (MethodCallExpr expr : methodCallExpr) {
            ResolvedMethodDeclaration rd = expr.resolve();
        }
    }
    
}
