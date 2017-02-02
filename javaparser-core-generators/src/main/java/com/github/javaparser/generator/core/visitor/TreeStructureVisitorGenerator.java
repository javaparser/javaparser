package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;

public class TreeStructureVisitorGenerator extends VisitorGenerator {
    public TreeStructureVisitorGenerator(JavaParser javaParser, SourceRoot sourceRoot) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor.treestructure", "TreeStructureVisitor", "void", "Context", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        final List<PropertyMetaModel> allPropertyMetaModels = node.getAllPropertyMetaModels();

        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        body.addStatement("callback.enterNode(n, arg.name, arg.indent);");

        for (PropertyMetaModel field : allPropertyMetaModels) {
            final String getter = field.getGetterMethodName();
            if (!field.isNode()) {
                body.addStatement(f("callback.outputProperty(n, \"%s\", n.%s(), arg.indent + 1);", field.getName(), getter));
            }
        }
        for (PropertyMetaModel field : allPropertyMetaModels) {
            final String getter = field.getGetterMethodName();
            if (field.isNode()) {
                if (field.isOptional()) {
                    body.addStatement(f("n.%s().ifPresent(c -> c.accept(this, new Context(\"%s\", arg.indent + 1)));", getter, field.getName()));
                } else {
                    body.addStatement(f("n.%s().accept(this, new Context(\"%s\", arg.indent + 1));", getter, field.getName()));
                }
            }
        }

        body.addStatement("callback.exitNode(n, arg.name, arg.indent);");
    }
}
