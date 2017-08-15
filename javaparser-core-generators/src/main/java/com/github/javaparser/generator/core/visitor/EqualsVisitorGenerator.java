package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Generates JavaParser's EqualsVisitor.
 */
public class EqualsVisitorGenerator extends VisitorGenerator {
    public EqualsVisitorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "EqualsVisitor", "Boolean", "Visitable", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        body.addStatement(f("final %s n2 = (%s) arg;", node.getTypeName(), node.getTypeName()));

        for (PropertyMetaModel field : node.getAllPropertyMetaModels()) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isNodeList()) {
                    body.addStatement(f("if (!nodesEquals(n.%s, n2.%s)) return false;", getter, getter));
                } else {
                    body.addStatement(f("if (!nodeEquals(n.%s, n2.%s)) return false;", getter, getter));
                }
            } else {
                body.addStatement(f("if (!objEquals(n.%s, n2.%s)) return false;", getter, getter));
            }
        }
        if (body.getStatements().size() == 1) {
            // Only the cast line was added, but nothing is using it, so remove it again.
            body.getStatements().clear();
        }
        body.addStatement("return true;");
    }
}
