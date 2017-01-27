package com.github.javaparser.generator.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;

/**
 * Generates JavaParser's VoidVisitor.
 */
public class VoidVisitorAdapterGenerator extends VisitorGenerator {
    VoidVisitorAdapterGenerator(JavaParser javaParser, SourceRoot sourceRoot, JavaParserMetaModel javaParserMetaModel) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "VoidVisitorAdapter", "void", "A", true, javaParserMetaModel);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, List<PropertyMetaModel> allPropertyMetaModels, CompilationUnit compilationUnit) {
        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        for (PropertyMetaModel field : allPropertyMetaModels) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isOptional() && field.isNodeList()) {
                    body.addStatement(f("n.%s.ifPresent( l -> l.forEach( v -> v.accept(this, arg)));", getter));
                } else if (field.isOptional()) {
                    body.addStatement(f("n.%s.ifPresent(l -> l.accept(this, arg));", getter));
                } else if (field.isNodeList()) {
                    body.addStatement(f("n.%s.forEach(p -> p.accept(this, arg));", getter));
                } else {
                    body.addStatement(f("n.%s.accept(this, arg);", getter));
                }
            }
        }
    }
}
