package com.github.javaparser.bootstrap;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.model.JavaParserMetaModel;
import com.github.javaparser.model.NodeMetaModel;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;

public class VisitorGenerator {
    private static JavaParserMetaModel javaParserMetaModel = new JavaParserMetaModel();

    public static void main(String[] args) throws IOException {
        final Path root = new File(VisitorGenerator.class.getProtectionDomain().getCodeSource().getLocation().getPath() + "/../../../javaparser-core/src/main/java/").toPath();

        JavaParser javaParser = new JavaParser();

        SourceRoot sourceRoot = new SourceRoot(root);

        CompilationUnit voidVisitorCu = sourceRoot.parse("com.github.javaparser.ast.visitor", "VoidVisitor.java", javaParser).get();

        ClassOrInterfaceDeclaration voidVisitor = voidVisitorCu.getInterfaceByName("VoidVisitor");
        voidVisitor.getMethods().forEach(m -> voidVisitor.getMembers().remove(m));

        for (NodeMetaModel node : javaParserMetaModel.getNodeMetaModels()) {
            if (!node.isAbstract()) {
                voidVisitor.addMethod("visit")
                        .addParameter(node.getClassName(), "n")
                        .addParameter("A", "arg")
                        .setBody(null);
            }
        }

        sourceRoot.save();

    }


}
