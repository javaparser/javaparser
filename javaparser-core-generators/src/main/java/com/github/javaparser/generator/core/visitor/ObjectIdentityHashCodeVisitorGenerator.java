package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

import java.util.List;

import static com.github.javaparser.JavaParser.parseStatement;

/**
 * Generates JavaParser's ObjectIdentityHashCodeVisitor.
 */
public class ObjectIdentityHashCodeVisitorGenerator extends VisitorGenerator {
    public ObjectIdentityHashCodeVisitorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "ObjectIdentityHashCodeVisitor", "Integer", "Void", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        final BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();
        body.addStatement("return n.hashCode();");
    }
}
