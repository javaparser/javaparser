package com.github.javaparser.generator.core.node;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.SourceRoot;

import static com.github.javaparser.JavaParser.parseBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class GetMetaModelGenerator extends NodeGenerator {
    public GetMetaModelGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        final MethodDeclaration getMetaModelMethod = (MethodDeclaration) parseBodyDeclaration(f("%s public %s getMetaModel() { return JavaParserMetaModel.%s; }",
                nodeMetaModel.isRootNode() ? "" : "@Override",
                nodeMetaModel.getClass().getSimpleName(),
                nodeMetaModel.getMetaModelFieldName()));

        addOrReplaceWhenSameSignature(nodeCoid, getMetaModelMethod);
        nodeCu.addImport(nodeMetaModel.getClass().getName());
        nodeCu.addImport(JavaParserMetaModel.class);
    }
}
