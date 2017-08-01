/**
 * (C) 2016 Agilysys NV, LLC.  All Rights Reserved.  Confidential Information of Agilysys NV, LLC.
 */
package com.foo;

import java.io.File;
import java.io.IOException;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Widget extends com.foo.base.Widget {
    private static final String PROJECT_ROOT = "/Users/peloquina/dev/javasymbolsolver-issue";
    private static final String JAVA_ROOT = PROJECT_ROOT + "/src/main/java";
    private static final String CLASS = JAVA_ROOT + "/com/foo/Widget.java";

    public static void main(String[] args) throws IOException, ParseException {
        File src = new File(JAVA_ROOT);
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver(true));
        combinedTypeSolver.add(new JavaParserTypeSolver(src));

        CompilationUnit compilationUnit = JavaParser.parse(new File(CLASS));

        JavaParserFacade parserFacade = JavaParserFacade.get(combinedTypeSolver);
        MethodDeclaration methodDeclaration = compilationUnit.getNodesByType(MethodDeclaration.class).stream()
              .filter(node -> node.getName().equals("doSomething")).findAny().orElse(null);
        methodDeclaration.getNodesByType(MethodCallExpr.class).forEach(parserFacade::solve);
    }

    public void doSomething() {
        doSomethingMore(new Widget());
    }

    public void doSomethingMore(Widget value) {
        // does something
    }
}
