package com.github.javaparser.generator.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.JavaParser.parseStatement;
import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.generator.utils.GeneratorUtils.f;

public class VisitorGenerator {
    private static JavaParserMetaModel javaParserMetaModel = new JavaParserMetaModel();

    public static void main(String[] args) throws IOException {
        final Path root = Paths.get(VisitorGenerator.class.getProtectionDomain().getCodeSource().getLocation().getPath(), "..", "..", "..", "javaparser-core", "src", "main", "java");

        JavaParser javaParser = new JavaParser();

        SourceRoot sourceRoot = new SourceRoot(root);

        generateVoidVisitor(javaParser, sourceRoot);
        generateHashcodeVisitor(javaParser, sourceRoot);

        sourceRoot.saveAll();
    }

    private static void generateHashcodeVisitor(JavaParser javaParser, SourceRoot sourceRoot) throws IOException {
        CompilationUnit voidVisitorCu = sourceRoot.parse("com.github.javaparser.ast.visitor", "HashCodeVisitor.java", javaParser).get();

        ClassOrInterfaceDeclaration voidVisitor = voidVisitorCu.getClassByName("HashCodeVisitor").get();
        voidVisitor.getMethods().forEach(m -> voidVisitor.getMembers().remove(m));

        for (BaseNodeMetaModel node : javaParserMetaModel.getNodeMetaModels()) {
            if (!node.isAbstract()) {
                MethodDeclaration visitMethod = voidVisitor.addMethod("visit", PUBLIC)
                        .addParameter(node.getName(), "n")
                        .addParameter("Void", "arg")
                        .setType(new ClassOrInterfaceType("Integer"));
                BlockStmt body = visitMethod.getBody().get();

                List<PropertyMetaModel> allPropertyMetaModels = new ArrayList<>(node.getPropertyMetaModels());
                BaseNodeMetaModel walkNode = node;
                while (walkNode.getSuperNodeMetaModel().isPresent()) {
                    walkNode = walkNode.getSuperNodeMetaModel().get();
                    allPropertyMetaModels.addAll(walkNode.getPropertyMetaModels());
                }
                
                if (allPropertyMetaModels.isEmpty()) {
                    body.addStatement(parseStatement("return 0;"));
                } else if (node.is(NodeList.class)) {
                    body.addStatement(parseStatement("return n.hashCode();"));
                } else {
                    String bodyBuilder = "return";
                    String prefix = "";
                    for (PropertyMetaModel field : allPropertyMetaModels) {

                        final String getter = field.getGetterMethodName() + "()";
                        // Is this field another AST node? Visit it.
                        if (field.isNode()) {
                            if (field.isOptional()) {
                                bodyBuilder += f("%s (n.%s.isPresent()? n.%s.get().accept(this, arg):0)", prefix, getter, getter);
                            } else {
                                bodyBuilder += f("%s (n.%s.accept(this, arg))", prefix, getter);
                            }
                        } else if (field.getType().equals(boolean.class)) {
                            bodyBuilder += f("%s (n.%s?1:0)", prefix, getter);
                        } else if (field.getType().equals(int.class)) {
                            bodyBuilder += f("%s n.%s", prefix, getter);
                        } else {
                            bodyBuilder += f("%s (n.%s.hashCode())", prefix, getter);
                        }
                        prefix = "* 31 +";
                    }
                    Statement returnStatement = parseStatement(bodyBuilder + ";");
                    body.addStatement(returnStatement);
                }
            }
        }
    }

    private static void generateVoidVisitor(JavaParser javaParser, SourceRoot sourceRoot) throws IOException {
        CompilationUnit voidVisitorCu = sourceRoot.parse("com.github.javaparser.ast.visitor", "VoidVisitor.java", javaParser).get();

        ClassOrInterfaceDeclaration voidVisitor = voidVisitorCu.getInterfaceByName("VoidVisitor").get();
        voidVisitor.getMethods().forEach(m -> voidVisitor.getMembers().remove(m));

        for (BaseNodeMetaModel node : javaParserMetaModel.getNodeMetaModels()) {
            if (!node.isAbstract()) {
                voidVisitor.addMethod("visit")
                        .addParameter(node.getName(), "n")
                        .addParameter("A", "arg")
                        .setBody(null);
            }
        }
    }
}
