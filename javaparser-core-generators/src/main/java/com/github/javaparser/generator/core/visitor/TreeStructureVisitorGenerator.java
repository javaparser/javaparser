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
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "TreeStructureVisitor", "void", "Integer", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        final List<PropertyMetaModel> allPropertyMetaModels = node.getAllPropertyMetaModels();
        
        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        body.addStatement("enterNode(n, arg);");

        for (PropertyMetaModel field : allPropertyMetaModels) {
            final String getter = field.getGetterMethodName() + "()";
            if (!field.getNodeReference().isPresent()) {
                body.addStatement(f("outputProperty(n, \"%s\", n.%s, arg +1);", field.getName(), getter));
            }
        }
        for (PropertyMetaModel field : allPropertyMetaModels) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isOptional()) {
                    body.addStatement(f("n.%s.ifPresent(c -> c.accept(this, arg + 1));", getter));
                } else {
                    body.addStatement(f("n.%s.accept(this, arg+1);", getter));
                }
            }
        }

        body.addStatement("exitNode(n, arg);");
    }
}
