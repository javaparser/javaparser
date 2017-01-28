package com.github.javaparser.generator.core.node;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.generator.utils.SeparatedItemStringBuilder;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

public class GetNodeListsGenerator extends NodeGenerator {
    public GetNodeListsGenerator(JavaParser javaParser, SourceRoot sourceRoot, JavaParserMetaModel javaParserMetaModel) {
        super(javaParser, sourceRoot, javaParserMetaModel);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        MethodDeclaration getNodeListsMethod = nodeCoid.getMethodsByName("getNodeLists").get(0);
        SeparatedItemStringBuilder statement = new SeparatedItemStringBuilder("return Arrays.asList(", ",", ");");
        for (PropertyMetaModel property : nodeMetaModel.getAllPropertyMetaModels()) {
            if (property.isNodeList()) {
                statement.append(property.getName());
            }
        }
        BlockStmt block = getNodeListsMethod.getBody().get();
        block.getStatements().clear();
        block.addStatement(statement.toString());
    }
}
