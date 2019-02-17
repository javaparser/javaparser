package com.github.javaparser.generator.core.node;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.utils.SourceRoot;

import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;

public class AcceptGenerator extends NodeGenerator {
    private final MethodDeclaration genericAccept;
    private final MethodDeclaration voidAccept;

    public AcceptGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
        genericAccept = parseBodyDeclaration("@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) { return v.visit(this, arg); }").asMethodDeclaration();
        voidAccept = parseBodyDeclaration("@Override public <A> void accept(final VoidVisitor<A> v, final A arg) { v.visit(this, arg); }").asMethodDeclaration();
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        if(nodeMetaModel.isAbstract()){
            return;
        }
        nodeCu.addImport(GenericVisitor.class);
        nodeCu.addImport(VoidVisitor.class);
        addOrReplaceWhenSameSignature(nodeCoid, genericAccept);
        addOrReplaceWhenSameSignature(nodeCoid, voidAccept);
    }
}
