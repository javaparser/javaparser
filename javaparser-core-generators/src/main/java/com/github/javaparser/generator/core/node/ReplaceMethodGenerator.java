package com.github.javaparser.generator.core.node;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SourceRoot;

import static com.github.javaparser.JavaParser.parseBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.capitalize;

public class ReplaceMethodGenerator extends NodeGenerator {
    public ReplaceMethodGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        MethodDeclaration replaceNodeMethod = (MethodDeclaration) parseBodyDeclaration("public boolean replace(Node node, Node replacementNode) {}");
        nodeCu.addImport(Node.class);
        nodeMetaModel.getSuperNodeMetaModel().ifPresent(s -> annotateOverridden(replaceNodeMethod));

        final BlockStmt body = replaceNodeMethod.getBody().get();

        body.addStatement("if (node == null) return false;");

        for (PropertyMetaModel property : nodeMetaModel.getDeclaredPropertyMetaModels()) {
            if (!property.isNode()) {
                continue;
            }
            String check;
            if (property.isNodeList()) {
                check = nodeListCheck(property);
            } else {
                check = attributeCheck(property, property.getSetterMethodName());
            }
            if (property.isOptional()) {
                check = f("if (%s != null) { %s }", property.getName(), check);
            }
            body.addStatement(check);
        }
        if (nodeMetaModel.getSuperNodeMetaModel().isPresent()) {
            body.addStatement("return super.replace(node, replacementNode);");
        } else {
            body.addStatement("return false;");
        }
        
        addOrReplaceWhenSameSignature(nodeCoid, replaceNodeMethod);
    }

    private String attributeCheck(PropertyMetaModel property, String attributeSetterName) {
        return f("if (node == %s) {" +
                "    %s((%s) replacementNode);" +
                "    return true;\n" +
                "}", property.getName(), attributeSetterName, property.getTypeName());
    }

    private String nodeListCheck(PropertyMetaModel property) {
        return f("for (int i = 0; i < %s.size(); i++) {" +
                "  if (%s.get(i) == node) {" +
                "    %s.set(i, (%s) replacementNode);" +
                "    return true;" +
                "  }" +
                "}", property.getName(), property.getName(), property.getName(), property.getTypeName());
    }
}
