/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

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

import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class ReplaceMethodGenerator extends NodeGenerator {
    public ReplaceMethodGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        MethodDeclaration replaceNodeMethod = (MethodDeclaration) parseBodyDeclaration("public boolean replace(Node node, Node replacementNode) {}");
        nodeCu.addImport(Node.class);
        annotateWhenOverridden(nodeMetaModel, replaceNodeMethod);

        final BlockStmt body = replaceNodeMethod.getBody().get();

        body.addStatement("if (node == null) { return false; }");

        int numberPropertiesDeclared = 0;
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
            numberPropertiesDeclared++;
        }
        if (nodeMetaModel.getSuperNodeMetaModel().isPresent()) {
            body.addStatement("return super.replace(node, replacementNode);");
        } else {
            body.addStatement("return false;");
        }

        if (!nodeMetaModel.isRootNode() && numberPropertiesDeclared == 0) {
            removeMethodWithSameSignature(nodeCoid, replaceNodeMethod);
        } else {
            addOrReplaceWhenSameSignature(nodeCoid, replaceNodeMethod);
        }
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
