package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.utils.CodeGenerationUtils;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.ProjectRoot;
import com.github.javaparser.utils.SourceRoot;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.Assert.assertTrue;

public class SymbolSolverCollectionStrategyTest {

    private final Path root = CodeGenerationUtils.mavenModuleRoot(JavaParser.class);
    private final ProjectRoot projectRoot = new SymbolSolverCollectionStrategy().collect(root);

    @Test
    public void resolveExpressions() throws IOException {
        System.out.println(projectRoot);
        SourceRoot sourceRoot = projectRoot.getSourceRoot(root.resolve("src/main/java")).get();
        AtomicInteger unresolved = new AtomicInteger();
        for (ParseResult<CompilationUnit> parseResult : sourceRoot.tryToParse()) {
            parseResult.ifSuccessful(compilationUnit -> {
                for (MethodDeclaration expr : compilationUnit.findAll(MethodDeclaration.class)) {
                    try {
                        expr.resolve().getQualifiedSignature();
                    } catch (UnsupportedOperationException e) {
                        // not supported operation, just skip
                    } catch (Exception e) {
                        unresolved.getAndIncrement();
                        Log.error(e, "Unable to resolve %s from %s", expr, compilationUnit.getStorage().get().getPath());
                    }
                }
            });
        }
        // not too many MethodDeclarations should be unresolved
        assertTrue(unresolved.get() < 10);
    }
}
