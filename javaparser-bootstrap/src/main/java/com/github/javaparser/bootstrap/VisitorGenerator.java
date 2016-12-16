package com.github.javaparser.bootstrap;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.model.JavaParserModel;
import com.github.javaparser.model.NodeModel;

import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.ast.NodeList.nodeList;

public class VisitorGenerator {
    private static JavaParserModel javaParserModel = new JavaParserModel();

    public static void main(String[] args) {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        cu.addImport("com.github.javaparser.ast.*");
        cu.addImport("com.github.javaparser.ast.body.*");
        cu.addImport("com.github.javaparser.ast.comments.*");
        cu.addImport("com.github.javaparser.ast.expr.*");
        cu.addImport("com.github.javaparser.ast.imports.*");
        cu.addImport("com.github.javaparser.ast.stmt.*");
        cu.addImport("com.github.javaparser.ast.type.*");

        ClassOrInterfaceDeclaration visitor = cu.addInterface("VoidVisitor", PUBLIC);
        visitor.setTypeParameters(nodeList(new TypeParameter("A")));

        for (NodeModel node : javaParserModel.getNodeModels()) {
            visitor.addMethod("visit")
                    .addParameter(node.getClassName(), "n")
                    .addParameter("A", "arg");
        }

        System.out.println(cu);
    }
}
