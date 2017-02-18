package com.github.javaparser.generator.core.node;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalBlockStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;
import java.util.function.Supplier;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.capitalize;


public class RemoveMethodGenerator extends NodeGenerator {
    public RemoveMethodGenerator(JavaParser javaParser, SourceRoot sourceRoot) {
        super(javaParser, sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        final MethodDeclaration removeMethod = getOrCreateMethod(nodeCoid, () -> {
                    nodeCu.addImport(Node.class);
                    return (MethodDeclaration) parseClassBodyDeclaration("@Override public boolean remove(Node node) {}");
                },
                "remove", "Node");

        final BlockStmt body = emptyBodyFor(removeMethod);

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
                String removeAttributeMethodName = generateRemoveMethodForAttribute(nodeCoid, nodeMetaModel, property);
                check = attributeCheck(property, removeAttributeMethodName);
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

    private BlockStmt emptyBodyFor(NodeWithOptionalBlockStmt<?> removeMethod) {
        final BlockStmt body = removeMethod.getBody().get();
        body.getStatements().clear();
        return body;
    }

    private MethodDeclaration getOrCreateMethod(ClassOrInterfaceDeclaration nodeCoid,
                                                Supplier<MethodDeclaration> newMethodSupplier,
                                                String methodName, String... methodParameterTypes) {
        final List<MethodDeclaration> removeMethods = nodeCoid.getMethodsBySignature(methodName, methodParameterTypes);
        final MethodDeclaration removeMethod;
        if (removeMethods.isEmpty()) {
            removeMethod = newMethodSupplier.get();
            nodeCoid.addMember(removeMethod);
        } else if (removeMethods.size() == 1) {
            removeMethod = removeMethods.get(0);
        } else {
            throw new AssertionError(f("Found more than one method while expecting only one."));
        }
        return removeMethod;
    }

    private String attributeCheck(PropertyMetaModel property, String removeAttributeMethodName) {
        return f("if (node == %s) {" +
                "    %s();" +
                "    return true;\n" +
                "}", property.getName(), removeAttributeMethodName);
    }

    private String nodeListCheck(PropertyMetaModel property) {
        return f("for (int i = 0; i < %s.cost(); i++) {" +
                "  if (%s.get(i) == node) {" +
                "    %s.remove(i);" +
                "    return true;" +
                "  }" +
                "}", property.getName(), property.getName(), property.getName());
    }

    private String generateRemoveMethodForAttribute(ClassOrInterfaceDeclaration nodeCoid, BaseNodeMetaModel nodeMetaModel, PropertyMetaModel property) {
        String methodName = "remove" + capitalize(property.getName());
        MethodDeclaration removeMethod = getOrCreateMethod(nodeCoid,
                () -> (MethodDeclaration) parseClassBodyDeclaration(f("public %s %s() {}", nodeMetaModel.getTypeName(), methodName)),
                methodName);
        BlockStmt block = emptyBodyFor(removeMethod);
        block.addStatement(f("return %s((%s) null);", property.getSetterMethodName(), property.getTypeNameForSetter()));
        return methodName;
    }
}
