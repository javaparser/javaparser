package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SourceRoot;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.metamodel.Multiplicity.ONE;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class TreeStructureVisitorGenerator extends VisitorGenerator {
    public TreeStructureVisitorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor.treestructure", "TreeStructureVisitor", "void", "Context", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        final List<PropertyMetaModel> allPropertyMetaModels = node.getAllPropertyMetaModels();

        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        final List<PropertyMetaModel> orderedProperties = new ArrayList<>();
        allPropertyMetaModels.stream().filter(PropertyMetaModel::isAttribute).filter(p -> p.getMultiplicity() == ONE).forEach(orderedProperties::add);
        allPropertyMetaModels.stream().filter(PropertyMetaModel::isNode).filter(p -> p.getMultiplicity() == ONE).forEach(orderedProperties::add);
        allPropertyMetaModels.stream().filter(PropertyMetaModel::isNodeList).forEach(orderedProperties::add);

        body.addStatement("callback.enterNode(n, arg.name, arg.indent);");

        for (PropertyMetaModel field : orderedProperties) {
            final String getter = field.getGetterMethodName();
            if (field.isNode()) {
                if (field.isOptional()) {
                    body.addStatement(f("n.%s().ifPresent(c -> c.accept(this, new Context(\"%s\", arg.indent + 1)));", getter, field.getName()));
                } else {
                    body.addStatement(f("n.%s().accept(this, new Context(\"%s\", arg.indent + 1));", getter, field.getName()));
                }
            } else {
                body.addStatement(f("callback.outputProperty(n, \"%s\", n.%s(), arg.indent + 1);", field.getName(), getter));
            }
        }

        body.addStatement("callback.exitNode(n, arg.name, arg.indent);");
    }
}
