package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Generates JavaParser's VoidVisitorAdapter.
 */
public class VoidVisitorAdapterGenerator extends VisitorGenerator {
    public VoidVisitorAdapterGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "VoidVisitorAdapter", "void", "A", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        for (PropertyMetaModel field : node.getAllPropertyMetaModels()) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isOptional() && field.isNodeList()) {
                    body.addStatement(f("n.%s.ifPresent( l -> l.forEach( v -> v.accept(this, arg)));", getter));
                } else if (field.isOptional()) {
                    body.addStatement(f("n.%s.ifPresent(l -> l.accept(this, arg));", getter));
                } else if (field.isNodeList()) {
                    body.addStatement(f("n.%s.forEach(p -> p.accept(this, arg));", getter));
                } else {
                    body.addStatement(f("n.%s.accept(this, arg);", getter));
                }
            }
        }
    }
}
