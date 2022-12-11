package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue1827Test extends AbstractResolutionTest {

    @Test
    public void solveParametrizedParametersConstructor() {
        
        String src = "public class ParametrizedParametersConstructor {\n"
                + "    public void foo() {\n"
                + "        EClass arg = new EClass();\n"
                + "        ParametrizedClass<String> pc = new ParametrizedClass<>(arg, arg);\n"
                + "    }\n"
                + "\n"
                + "    class EClass implements BaseType<String> {\n"
                + "    }\n"
                + "}\n"
                + "\n"
                + "class ParametrizedClass<T> {\n"
                + "    public ParametrizedClass(BaseType<T> arg1, BaseType<T> arg2) {\n"
                + "    }\n"
                + "}\n"
                + "\n"
                + "interface BaseType<T> {\n"
                + "}";
        
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
        StaticJavaParser
                .getConfiguration()
                .setSymbolResolver(symbolSolver);
        CompilationUnit cu = StaticJavaParser.parse(src);
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ParametrizedParametersConstructor");
        ObjectCreationExpr oce = clazz.findAll(ObjectCreationExpr.class).get(1); // new ParametrizedClass<>(arg, arg)
        assertDoesNotThrow(() -> oce.resolve());
    }

}
