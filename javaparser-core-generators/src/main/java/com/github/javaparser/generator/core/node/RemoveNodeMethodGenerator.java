package com.github.javaparser.generator.core.node;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;


public class RemoveNodeMethodGenerator extends NodeGenerator {
    public RemoveNodeMethodGenerator(JavaParser javaParser, SourceRoot sourceRoot) {
        super(javaParser, sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        final List<MethodDeclaration> removeMethods = nodeCoid.getMethodsBySignature("remove", "Node");
        final MethodDeclaration removeMethod;
        if (removeMethods.isEmpty()) {
            nodeCu.addImport(Node.class);
            removeMethod = (MethodDeclaration) JavaParser.parseClassBodyDeclaration("@Override public boolean remove(Node node) {}");
            nodeCoid.addMember(removeMethod);
        } else if (removeMethods.size() == 1) {
            removeMethod = removeMethods.get(0);
        } else {
            throw new AssertionError(f("Not exactly one remove node method exists: %s", nodeMetaModel.getTypeName()));
        }

        final BlockStmt body = removeMethod.getBody().get();
        body.getStatements().clear();

        body.addStatement("if (node == null) return false;");

        for (PropertyMetaModel property : nodeMetaModel.getDeclaredPropertyMetaModels()) {
            if (!property.isNode()) {
                continue;
            }
            String check;
            if (property.isNodeList()) {
                check = nodeListCheck(property);
            } else {
                if (property.isRequired()) {
                    continue;
                }
                check = fieldCheck(property);
            }
            if (property.isOptional()) {
                check = f("if (%s != null) { %s }", property.getName(), check);
            }
            body.addStatement(check);
        }
        if (nodeMetaModel.getSuperNodeMetaModel().isPresent()) {
            body.addStatement("return super.remove(node);");
        } else {
            body.addStatement("return false;");
        }
    }

    private String fieldCheck(PropertyMetaModel property) {
        return f("if (node == %s) {" +
                "    %s((%s) null);" +
                "    return true;" +
                "}", property.getName(), property.getSetterMethodName(), property.getTypeNameForSetter());
    }

    private String nodeListCheck(PropertyMetaModel property) {
        return f("for (int i = 0; i < %s.size(); i++) {\n" +
                "  if (%s.get(i) == node) {\n" +
                "    %s.remove(i);\n" +
                "    return true;\n" +
                "  }" +
                "}", property.getName(), property.getName(), property.getName());
    }
}
