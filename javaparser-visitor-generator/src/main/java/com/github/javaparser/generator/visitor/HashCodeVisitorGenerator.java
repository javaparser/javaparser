package com.github.javaparser.generator.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.JavaParser.parseStatement;
import static com.github.javaparser.generator.utils.GeneratorUtils.f;

public class HashCodeVisitorGenerator extends VisitorGenerator {
    public HashCodeVisitorGenerator(JavaParser javaParser, SourceRoot sourceRoot, JavaParserMetaModel javaParserMetaModel) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "HashCodeVisitor", javaParserMetaModel);
    }

    @Override
    protected String getReturnType() {
        return "Integer";
    }

    @Override
    protected String getArgumentType() {
        return "Void";
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        List<PropertyMetaModel> allPropertyMetaModels = new ArrayList<>(node.getPropertyMetaModels());
        BaseNodeMetaModel walkNode = node;
        while (walkNode.getSuperNodeMetaModel().isPresent()) {
            walkNode = walkNode.getSuperNodeMetaModel().get();
            allPropertyMetaModels.addAll(walkNode.getPropertyMetaModels());
        }

        if (allPropertyMetaModels.isEmpty()) {
            body.addStatement(parseStatement("return 0;"));
        } else {
            String bodyBuilder = "return";
            String prefix = "";
            for (PropertyMetaModel field : allPropertyMetaModels) {

                final String getter = field.getGetterMethodName() + "()";
                // Is this field another AST node? Visit it.
                if (field.getNodeReference().isPresent()) {
                    if (field.isOptional()) {
                        bodyBuilder += f("%s (n.%s.isPresent()? n.%s.get().accept(this, arg):0)", prefix, getter, getter);
                    } else {
                        bodyBuilder += f("%s (n.%s.accept(this, arg))", prefix, getter);
                    }
                } else {
                    Class<?> type = field.getType();
                    if (type.equals(boolean.class)) {
                        bodyBuilder += f("%s (n.%s?1:0)", prefix, getter);
                    } else if (type.equals(int.class)) {
                        bodyBuilder += f("%s n.%s", prefix, getter);
                    } else {
                        bodyBuilder += f("%s (n.%s.hashCode())", prefix, getter);
                    }
                }
                prefix = "* 31 +";
            }
            Statement returnStatement = parseStatement(bodyBuilder + ";");
            body.addStatement(returnStatement);
        }
    }

}
