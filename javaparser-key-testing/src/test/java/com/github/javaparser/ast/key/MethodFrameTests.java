package com.github.javaparser.ast.key;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.google.common.truth.Truth;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class MethodFrameTests {
    @Test
    void mftest1() throws IOException {
        loadAndResolveAll(new File("src/test/resources/nameResolution/A.java"));
    }

    @Test
    void mftestB() throws IOException {
        loadAndResolveAll(new File("src/test/resources/nameResolution/B.java"));
    }

    private void loadAndResolveAll(File file) throws IOException {
        final ParserConfiguration configuration = new ParserConfiguration();
        configuration.setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(
                new JavaParserTypeSolver(file.getParentFile()),
                new ClassLoaderTypeSolver(ClassLoader.getSystemClassLoader()))));
        JavaParser parser = new JavaParser(configuration);

        ParseResult<CompilationUnit> cu = parser.parse(file);
        if (!cu.isSuccessful()) {
            for (Problem problem : cu.getProblems()) {
                System.out.println(problem);
            }
            Assertions.fail("Errors during parsing");
        }

        final ResolveAllVisitor v = new ResolveAllVisitor();
        cu.getResult().get().accept(v, null);

        Set<String> errorLines = Files.readAllLines(file.toPath()).stream()
                .filter(it -> it.trim().startsWith("//?"))
                .map(it -> it.trim().substring(4).trim())
                .collect(Collectors.toSet());

        errorLines.stream().sorted().forEach(errorLine -> System.out.format("//? %s%n", errorLine));
        System.out.println("---");
        v.messages.stream().sorted().forEach(errorLine -> System.out.format("//? %s%n", errorLine));

        Truth.assertThat(v.messages).isEqualTo(errorLines);
    }

    private static class ResolveAllVisitor extends VoidVisitorAdapter<Void> {
        final Set<String> messages = new TreeSet<>();

        @Override
        public void visit(NameExpr n, Void arg) {
            resolve(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(FieldAccessExpr n, Void arg) {
            resolve(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(MethodCallExpr n, Void arg) {
            resolve(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ObjectCreationExpr n, Void arg) {
            resolve(n);
            super.visit(n, arg);
        }

        public <T extends ResolvedDeclaration, N extends Expression & Resolvable<T>> void resolve(N n) {
            Path base = n.findCompilationUnit()
                    .flatMap(CompilationUnit::getStorage)
                    .map(it -> it.getPath().getParent())
                    .get();
            String pos = n.getRange().map(it -> it.begin.toString()).orElse("_");

            try {
                ResolvedDeclaration rtype = n.resolve();
                String target;
                try {
                    Node t = rtype.toAst().get();
                    target = t.getRange().map(it -> it.begin.toString()).orElse("_");
                    target += " in "
                            + t.findCompilationUnit()
                                    .flatMap(CompilationUnit::getStorage)
                                    .map(it -> base.relativize(it.getPath()).toString())
                                    .orElse(null);
                } catch (NoSuchElementException e) {
                    target = "_";
                }

                messages.add(String.format("name: %s@%s refers to %s@%s", n, pos, rtype.getName(), target));
                try {
                    var x = n.getSymbolResolver().calculateType(n);
                    messages.add(String.format("type: %s@%s refers to %s", n, pos, x));
                } catch (UnsolvedSymbolException e) {
                    messages.add(String.format("ERROR type: %s@%s", n, pos));
                }
            } catch (UnsolvedSymbolException e) {
                messages.add(String.format("ERROR name: %s@%s", n, pos));
            }
        }
    }
}
