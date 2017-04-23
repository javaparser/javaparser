package com.github.javaparser.generator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.utils.SourceRoot;

import javax.annotation.Generated;

import static com.github.javaparser.ast.NodeList.toNodeList;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * A general pattern that the generators in this module will follow.
 */
public abstract class Generator {
    protected final SourceRoot sourceRoot;

    protected Generator(SourceRoot sourceRoot) {
        this.sourceRoot = sourceRoot;
    }

    public abstract void generate() throws Exception;

    protected <T extends Node & NodeWithAnnotations<T>> void annotateGenerated(T node) {
        annotate(node, Generated.class, new StringLiteralExpr(getClass().getName()));
    }

    protected <T extends Node & NodeWithAnnotations<T>> void annotateSuppressWarnings(T node) {
        annotate(node, SuppressWarnings.class, new StringLiteralExpr("unchecked"));
    }

    private <T extends Node & NodeWithAnnotations<T>> void annotate(T node, Class<?> annotation, Expression content) {
        node.setAnnotations(
                node.getAnnotations().stream()
                        .filter(a -> !a.getNameAsString().equals(annotation.getSimpleName()))
                        .collect(toNodeList()));

        node.addSingleMemberAnnotation(annotation.getSimpleName(), content);
        node.tryAddImportToParentCompilationUnit(annotation);
    }
    
    
}
