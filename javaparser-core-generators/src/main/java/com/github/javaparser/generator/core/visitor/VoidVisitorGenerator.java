package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;

/**
 * Generates JavaParser's VoidVisitor.
 */
public class VoidVisitorGenerator extends VisitorGenerator {
    public VoidVisitorGenerator(JavaParser javaParser, SourceRoot sourceRoot) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "VoidVisitor", "void", "A", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        visitMethod.setBody(null);
    }
}
