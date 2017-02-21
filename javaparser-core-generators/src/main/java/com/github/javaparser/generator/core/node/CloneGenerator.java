package com.github.javaparser.generator.core.node;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;

import static com.github.javaparser.JavaParser.parseClassBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class CloneGenerator extends NodeGenerator {
    public CloneGenerator(JavaParser javaParser, SourceRoot sourceRoot) {
        super(javaParser, sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        nodeCoid.getMethodsByName("clone").forEach(Node::remove);

        nodeCu.addImport(CloneVisitor.class);
        nodeCoid.addMember(parseClassBodyDeclaration(f(
                "@Override public %s clone() { return (%s) accept(new CloneVisitor(), null); }",
                nodeMetaModel.getTypeNameGenerified(),
                nodeMetaModel.getTypeNameGenerified()
        )));
    }
}
