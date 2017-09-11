package com.github.javaparser.generator.core.node;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

import static com.github.javaparser.JavaParser.parseBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class GetNodeListsGenerator extends NodeGenerator {
    public GetNodeListsGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        if (nodeMetaModel.isAbstract()) {
            return;
        }

        SeparatedItemStringBuilder statement = new SeparatedItemStringBuilder("return Arrays.asList(", ",", ");");
        for (PropertyMetaModel property : nodeMetaModel.getAllPropertyMetaModels()) {
            if (property.isNodeList()) {
                if (property.isOptional()) {
                    statement.append(f("%s().orElse(null)", property.getGetterMethodName()));
                } else {
                    statement.append(f("%s()", property.getGetterMethodName()));
                }
            }
        }
        
        if (!statement.hasItems()) {
            return;
        }

        final MethodDeclaration getNodeListsMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public List<NodeList<?>> getNodeLists() {%s}", statement));
        removeMethodWithSameSignature(nodeCoid, getNodeListsMethod);
        annotateGenerated(getNodeListsMethod);
    }
}
