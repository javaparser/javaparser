package com.github.javaparser.generator.core.node;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.utils.SourceRoot;

import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class CloneGenerator extends NodeGenerator {
    public CloneGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        nodeCu.addImport(CloneVisitor.class);
        MethodDeclaration cloneMethod = (MethodDeclaration) parseBodyDeclaration(f(
                "@Override public %s clone() { return (%s) accept(new CloneVisitor(), null); }",
                nodeMetaModel.getTypeNameGenerified(),
                nodeMetaModel.getTypeNameGenerified()
        ));
        addOrReplaceWhenSameSignature(nodeCoid, cloneMethod);
    }
}
