package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.FileNotFoundException;

import static com.github.javaparser.StaticJavaParser.parse;

class Issue1491Test {

    @Test
    void verifyIssue1491SolvingClassInSameFile() throws FileNotFoundException {
        File aJava = new File("src/test/resources/issue1491/A.java");
        if (!aJava.exists()) {
            throw new IllegalStateException();
        }

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(aJava.getAbsoluteFile().getParentFile()));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        StaticJavaParser.setConfiguration(parserConfiguration);

        CompilationUnit cu = parse(aJava);
        cu.accept(new VoidVisitorAdapter() {
            public void visit(NameExpr n, Object arg) {
                ResolvedType type = JavaParserFacade.get(localCts)
                        .getType(n);
                super.visit(n, arg);
            }
        }, null);
    }

    @Test
    void verifyIssue1491ResolvingStaticMethodCalls() throws FileNotFoundException {
        File aJava = new File("src/test/resources/issue1491/A.java");
        if (!aJava.exists()) {
            throw new IllegalStateException();
        }

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(aJava.getAbsoluteFile().getParentFile()));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        StaticJavaParser.setConfiguration(parserConfiguration);

        CompilationUnit cu = parse(aJava);
        cu.accept(new VoidVisitorAdapter() {

            public void visit(MethodCallExpr n, Object arg) {
                ResolvedMethodDeclaration decl = JavaParserFacade.get(localCts).solve(n).getCorrespondingDeclaration();
                super.visit(n, arg);
            }
        }, null);
    }

    @Test
    void verifyIssue1491Combined() throws FileNotFoundException {
        File aJava = new File("src/test/resources/issue1491/A.java");
        if (!aJava.exists()) {
            throw new IllegalStateException();
        }

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(aJava.getAbsoluteFile().getParentFile()));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        StaticJavaParser.setConfiguration(parserConfiguration);

        CompilationUnit cu = parse(aJava);
        cu.accept(new VoidVisitorAdapter<Void>() {
            public void visit(NameExpr n, Void arg) {
                try {
                    ResolvedType type = JavaParserFacade.get(localCts).getType(n);
                } catch (UnsolvedSymbolException e) {
                    throw new RuntimeException("Unable to solve name expr at " + n.getRange(), e);
                }
                super.visit(n, arg);
            }

            public void visit(MethodCallExpr n, Void arg) {
                ResolvedMethodDeclaration decl = JavaParserFacade.get(localCts).solve(n).getCorrespondingDeclaration();
                super.visit(n, arg);
            }
        }, null);
    }

}