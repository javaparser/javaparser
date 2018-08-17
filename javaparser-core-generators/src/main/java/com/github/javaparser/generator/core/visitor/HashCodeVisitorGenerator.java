package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

import static com.github.javaparser.JavaParser.parseStatement;

/**
 * Generates JavaParser's HashCodeVisitor.
 */
public class HashCodeVisitorGenerator extends VisitorGenerator {
    public HashCodeVisitorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot, "com.github.javaparser.ast.visitor", "HashCodeVisitor", "Integer", "Void", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        final BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        final SeparatedItemStringBuilder builder = new SeparatedItemStringBuilder("return ", "* 31 +", ";");
        final List<PropertyMetaModel> propertyMetaModels= node.getAllPropertyMetaModels();
        if (propertyMetaModels.isEmpty()) {
            builder.append("0");
        } else {
            for (PropertyMetaModel field : propertyMetaModels) {
                final String getter = field.getGetterMethodName() + "()";
                // Is this field another AST node? Visit it.
                if (field.getNodeReference().isPresent()) {
                    if (field.isOptional()) {
                        builder.append("(n.%s.isPresent()? n.%s.get().accept(this, arg):0)", getter, getter);
                    } else {
                        builder.append("(n.%s.accept(this, arg))", getter);
                    }
                } else {
                    Class<?> type = field.getType();
                    if (type.equals(boolean.class)) {
                        builder.append("(n.%s?1:0)", getter);
                    } else if (type.equals(int.class)) {
                        builder.append("n.%s", getter);
                    } else {
                        builder.append("(n.%s.hashCode())", getter);
                    }
                }
            }
        }
        body.addStatement(parseStatement(builder.toString()));
    }
}
