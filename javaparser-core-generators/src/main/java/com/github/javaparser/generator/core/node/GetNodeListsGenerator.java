package com.github.javaparser.generator.core.node;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

import static com.github.javaparser.JavaParser.parseClassBodyDeclaration;
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

        List<MethodDeclaration> getNodeListsMethods = nodeCoid.getMethodsByName("getNodeLists");
        if (!statement.hasItems()) {
            getNodeListsMethods.forEach(Node::remove);
            return;
        }

        if (getNodeListsMethods.isEmpty()) {
            nodeCoid.addMember(parseClassBodyDeclaration(f("@Override public List<NodeList<?>> getNodeLists() {%s}", statement)));
            return;
        }

        BlockStmt block = getNodeListsMethods.get(0).getBody().get();
        block.getStatements().clear();
        block.addStatement(statement.toString());
    }
}
