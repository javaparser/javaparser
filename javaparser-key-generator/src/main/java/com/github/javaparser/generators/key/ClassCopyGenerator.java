package com.github.javaparser.generators.key;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.generator.Generator;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public abstract class ClassCopyGenerator extends Generator {
    protected final Path output;
    private final Class<?>[] classes;

    public ClassCopyGenerator(SourceRoot sourceRoot, Path outputDirectory, Class<?>[] classes) {
        super(sourceRoot);
        output = outputDirectory;
        this.classes = classes;
    }

    public final void generate() {
        Log.info("Running %s", () -> getClass().getSimpleName());
        for (var visitor : classes) {
            Pair<CompilationUnit, ClassOrInterfaceDeclaration> result = parseClass(visitor);
            generateClass(result.a, result.b);
        }
    }

    protected abstract void generateClass(CompilationUnit unit, ClassOrInterfaceDeclaration type);

    protected Pair<CompilationUnit, ClassOrInterfaceDeclaration> parseClass(Class<?> fqn) {
        CompilationUnit nodeCu = sourceRoot.parse(fqn.getPackageName(), fqn.getSimpleName() + ".java")
                .clone(); //Don't change the original file
        ClassOrInterfaceDeclaration nodeCoid = (ClassOrInterfaceDeclaration) nodeCu.getPrimaryType().get();
        //.getClassByName(fqn.getSimpleName())
        //        .orElseThrow(() -> new AssertionError("Can't find class: " + fqn));
        return new Pair<>(nodeCu, nodeCoid);
    }
}
