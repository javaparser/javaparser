package com.github.javaparser.generator.core.node;

import com.github.javaparser.Tokens;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

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
                .addParameter(Tokens.class, "tokens");


        BlockStmt body = constructor.getBody();

        SeparatedItemStringBuilder superCall = new SeparatedItemStringBuilder("super(", ", ", ");");
        superCall.append("tokens");
        for (PropertyMetaModel parameter : nodeMetaModel.getConstructorParameters()) {
            constructor.addParameter(parameter.getTypeNameForSetter(), parameter.getName());
            if (nodeMetaModel.getDeclaredPropertyMetaModels().contains(parameter)) {
                body.addStatement(parseStatement(f("%s(%s);", parameter.getSetterMethodName(), parameter.getName())));
            } else {
                superCall.append(parameter.getName());
            }
        }

        body.getStatements().add(0, parseExplicitConstructorInvocationStmt(superCall.toString()));

        ConstructorDeclaration existingConstructorDeclaration = nodeCoid.getConstructors().get(nodeCoid.getConstructors().size() - 1);
        nodeCoid.getMembers().replace(existingConstructorDeclaration, constructor);
        nodeCu.addImport(Tokens.class);
    }
}
