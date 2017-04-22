package com.github.javaparser.generator.core.node;

import com.github.javaparser.Range;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

import javax.annotation.Generated;
import java.util.Optional;

import static com.github.javaparser.JavaParser.parseExplicitConstructorInvocationStmt;
import static com.github.javaparser.JavaParser.parseStatement;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class MainConstructorGenerator extends NodeGenerator {
    public MainConstructorGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        if (nodeMetaModel.is(Node.class)) {
            return;
        }
        ConstructorDeclaration constructor = new ConstructorDeclaration()
                .setPublic(true)
                .setName(nodeCoid.getNameAsString())
                .addParameter(Range.class, "range")
                .addSingleMemberAnnotation(Generated.class, getClass().getName());


        BlockStmt body = constructor.getBody();

        SeparatedItemStringBuilder superCall = new SeparatedItemStringBuilder("super(", ", ", ");");
        superCall.append("range");
        for (PropertyMetaModel parameter : nodeMetaModel.getConstructorParameters()) {
            constructor.addParameter(parameter.getTypeNameForSetter(), parameter.getName());
            if (nodeMetaModel.getDeclaredPropertyMetaModels().contains(parameter)) {
                body.addStatement(parseStatement(f("%s(%s);", parameter.getSetterMethodName(), parameter.getName())));
            } else {
                superCall.append(parameter.getName());
            }
        }

        body.getStatements().add(0, parseExplicitConstructorInvocationStmt(superCall.toString()));

        nodeCoid.getMembers().stream()
                .filter(m -> m instanceof CallableDeclaration)
                .map(m -> ((CallableDeclaration) m))
                .filter(m -> m.getSignature().equals(constructor.getSignature()))
                .findFirst()
                .ifPresent(m -> nodeCoid.getMembers().replace(m, constructor));
        nodeCu.addImport(Range.class);
    }
}
