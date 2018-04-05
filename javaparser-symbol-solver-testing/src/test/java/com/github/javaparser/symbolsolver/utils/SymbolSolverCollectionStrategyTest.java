package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.utils.*;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Optional;

import static org.junit.Assert.assertTrue;

public class SymbolSolverCollectionStrategyTest {

    private final Path root = CodeGenerationUtils.mavenModuleRoot(SymbolSolverCollectionStrategyTest.class).resolve("").getParent();
    private final ProjectRoot projectRoot = new CollectionContext(new SymbolSolverCollectionStrategy()).collect(root);

    @Test
    public void resolveExpressions() throws IOException {
        Optional<SourceRoot> sourceRoot = projectRoot.getSourceRoot(root.resolve("javaparser-core/src/main/java"));
        assertTrue(sourceRoot.isPresent());
        int unresolved = 0;
        for (ParseResult<CompilationUnit> parseResult : sourceRoot.get().tryToParse()) {
            CompilationUnit compilationUnit = parseResult.getResult().get();
            for (MethodDeclaration expr : compilationUnit.findAll(MethodDeclaration.class)) {
                try {
                    expr.resolve().getQualifiedSignature();
                } catch (UnsupportedOperationException e) {
                    // not supported operation, just skip
                } catch (Exception e) {
                    unresolved++;
                    Log.error(e, "Unable to resolve %s from %s", expr, compilationUnit.getStorage().get().getPath());
                }
            }
        }
        // not too many MethodDeclarations should be unresolved
        assertTrue(unresolved < 10);
    }
}
