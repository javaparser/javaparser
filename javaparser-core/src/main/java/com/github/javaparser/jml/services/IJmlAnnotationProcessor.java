package com.github.javaparser.jml.services;

import com.github.javaparser.ast.CompilationUnit;
import org.jetbrains.annotations.NotNull;

/**
 * This service provides support for handling with annotation inside parsed AST.
 *
 * @author Alexander Weigl
 * @version 1 (1/31/20)
 */
public interface IJmlAnnotationProcessor {
    /**
     * Processing of the given compilation unit.
     * This method should find appropriate annotation
     * inside the given {@ast} and translate them into
     * JML specification.
     *
     * @param ast
     */
    void process(@NotNull CompilationUnit ast);
}
