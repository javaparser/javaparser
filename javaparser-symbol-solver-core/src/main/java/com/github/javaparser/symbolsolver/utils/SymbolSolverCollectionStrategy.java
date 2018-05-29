package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.ParserCollectionStrategy;
import com.github.javaparser.utils.ProjectRoot;

import java.io.IOException;
import java.nio.file.Path;

/**
 * Attempts to configure the symbol solver to look at the source code and jar files found in a project directory.
 */
public class SymbolSolverCollectionStrategy {

    private final ParserConfiguration parserConfiguration;
    private final CombinedTypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(false));

    public SymbolSolverCollectionStrategy() {
        this(new ParserConfiguration());
    }

    public SymbolSolverCollectionStrategy(ParserConfiguration parserConfiguration) {
        this.parserConfiguration = parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
    }

    public ProjectRoot collect(Path path) {
        ProjectRoot projectRoot = new ParserCollectionStrategy(parserConfiguration).collect(path);
        projectRoot.getSourceRoots().forEach(sourceRoot -> typeSolver.add(new JavaParserTypeSolver(sourceRoot.getRoot())));
        projectRoot.getJarFiles().forEach(jarFile -> {
            try {
                typeSolver.add(new JarTypeSolver(jarFile));
            } catch (IOException e) {
                throw new RuntimeException("Something went wrong while configuring the symbol solver.", e);
            }
        });
        return projectRoot;
    }
}
