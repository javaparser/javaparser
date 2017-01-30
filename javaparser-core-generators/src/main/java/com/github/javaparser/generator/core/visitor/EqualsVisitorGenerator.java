package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;

/**
 * Generates JavaParser's EqualsVisitor.
 */
public class EqualsVisitorGenerator extends VisitorGenerator {
    public EqualsVisitorGenerator(JavaParser javaParser, SourceRoot sourceRoot) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "EqualsVisitor", "Boolean", "Node", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        body.addStatement(f("final %s n2 = (%s) arg;", node.getTypeName(), node.getTypeName()));

        for (PropertyMetaModel field : node.getAllPropertyMetaModels()) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isNodeList()) {
                    body.addStatement(f("if (!nodesEquals(n1.%s, n2.%s)) return false;", getter, getter));
                } else {
                    body.addStatement(f("if (!nodeEquals(n1.%s, n2.%s)) return false;", getter, getter));
                }
            } else {
                body.addStatement(f("if (!objEquals(n1.%s, n2.%s)) return false;", getter, getter));
            }
        }
        if (body.getStatements().size() == 1) {
            // Only the cast line was added, but nothing is using it, so remove it again.
            body.getStatements().clear();
        }
        body.addStatement("return true;");
    }
}
