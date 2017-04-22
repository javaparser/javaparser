package com.github.javaparser.generator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.utils.SourceRoot;

import javax.annotation.Generated;

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

    protected <T extends Node & NodeWithAnnotations> void markGenerated(T node) {
        node.addSingleMemberAnnotation(Generated.class, f("\"%s\"", getClass().getName()));
        node.tryAddImportToParentCompilationUnit(Generated.class);
    }
}
