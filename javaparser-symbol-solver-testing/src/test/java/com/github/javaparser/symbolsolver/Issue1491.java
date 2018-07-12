package com.github.javaparser.symbolsolver;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

public class Issue1491 {

    @Test
    public void verifyIssue1491SolvingClassInSameFile() throws FileNotFoundException {
        File aJava = new File("src/test/resources/issue1491/A.java");
        if (!aJava.exists()) {
            throw new IllegalStateException();
        }

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(aJava.getAbsoluteFile().getParentFile()));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser.setStaticConfiguration(parserConfiguration);

        CompilationUnit cu = JavaParser.parse(aJava);
        cu.accept(new VoidVisitorAdapter() {
            public void visit(NameExpr n, Object arg) {
                ResolvedType type = JavaParserFacade.get(localCts)
                            .getType(n);
                super.visit(n, arg);
            }
        }, null);
    }

    @Test
    public void verifyIssue1491ResolvingStaticMethodCalls() throws FileNotFoundException {
        File aJava = new File("src/test/resources/issue1491/A.java");
        if (!aJava.exists()) {
            throw new IllegalStateException();
        }

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(aJava.getAbsoluteFile().getParentFile()));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser.setStaticConfiguration(parserConfiguration);

        CompilationUnit cu = JavaParser.parse(aJava);
        cu.accept(new VoidVisitorAdapter() {

            public void visit(MethodCallExpr n, Object arg) {
                ResolvedMethodDeclaration decl = JavaParserFacade.get(localCts).solve(n).getCorrespondingDeclaration();
                super.visit(n, arg);
            }
        }, null);
    }

    @Test
    public void verifyIssue1491Combined() throws FileNotFoundException {
        File aJava = new File("src/test/resources/issue1491/A.java");
        if (!aJava.exists()) {
            throw new IllegalStateException();
        }

        CombinedTypeSolver localCts = new CombinedTypeSolver();
        localCts.add(new ReflectionTypeSolver());
        localCts.add(new JavaParserTypeSolver(aJava.getAbsoluteFile().getParentFile()));

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(localCts));
        JavaParser.setStaticConfiguration(parserConfiguration);

        CompilationUnit cu = JavaParser.parse(aJava);
        cu.accept(new VoidVisitorAdapter() {
            public void visit(NameExpr n, Object arg) {
                try {
                    ResolvedType type = JavaParserFacade.get(localCts).getType(n);
                } catch (UnsolvedSymbolException e) {
                    throw new RuntimeException("Unable to solve name expr at " + n.getRange(), e);
                }
                super.visit(n, arg);
            }

            public void visit(MethodCallExpr n, Object arg) {
                ResolvedMethodDeclaration decl = JavaParserFacade.get(localCts).solve(n).getCorrespondingDeclaration();
                super.visit(n, arg);
            }
        }, null);
    }

}