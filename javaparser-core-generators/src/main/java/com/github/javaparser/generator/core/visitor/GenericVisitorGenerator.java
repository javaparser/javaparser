package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;

/**
 * Generates JavaParser's GenericVisitor.
 */
public class GenericVisitorGenerator extends VisitorGenerator {
    public GenericVisitorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "GenericVisitor", "R", "A", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(false));
        
        visitMethod.setBody(null);
    }
}
