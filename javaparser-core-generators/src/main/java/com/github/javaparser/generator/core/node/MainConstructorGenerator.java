package com.github.javaparser.generator.core.node;

import com.github.javaparser.Range;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

import java.util.List;

import static com.github.javaparser.JavaParser.parseExplicitConstructorInvocationStmt;
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
                .addParameter(TokenRange.class, "tokenRange")
                .setJavadocComment("This constructor is used by the parser and is considered private.");

        BlockStmt body = constructor.getBody();

        SeparatedItemStringBuilder superCall = new SeparatedItemStringBuilder("super(", ", ", ");");
        superCall.append("tokenRange");
        for (PropertyMetaModel parameter : nodeMetaModel.getConstructorParameters()) {
            constructor.addParameter(parameter.getTypeNameForSetter(), parameter.getName());
            if (nodeMetaModel.getDeclaredPropertyMetaModels().contains(parameter)) {
                body.addStatement(f("%s(%s);", parameter.getSetterMethodName(), parameter.getName()));
            } else {
                superCall.append(parameter.getName());
            }
        }

        body.getStatements().add(0, parseExplicitConstructorInvocationStmt(superCall.toString()));

        body.addStatement("customInitialization();");

        ConstructorDeclaration rangeConstructor = constructor.clone();
        rangeConstructor.getParameter(0).setType(Range.class);

        replaceWhenSameSignature(nodeCoid, rangeConstructor, constructor);
        nodeCu.addImport(TokenRange.class);
        annotateGenerated(constructor);
    }

    protected void replaceWhenSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callableWithSignature, CallableDeclaration<?> callableToReplaceWith) {
        final List<CallableDeclaration<?>> existingCallables = containingClassOrInterface.getCallablesWithSignature(callableWithSignature.getSignature());
        if (existingCallables.isEmpty()) {
            throw new AssertionError(f("Wanted to regenerate a method with signature %s in %s, but it wasn't there.", callableWithSignature.getSignature(), containingClassOrInterface.getNameAsString()));
        }
        if (existingCallables.size() > 1) {
            throw new AssertionError(f("Wanted to regenerate a method with signature %s in %s, but found more than one.", callableWithSignature.getSignature(), containingClassOrInterface.getNameAsString()));
        }
        final CallableDeclaration<?> existingCallable = existingCallables.get(0);
        callableToReplaceWith.setJavadocComment(callableToReplaceWith.getJavadocComment().orElse(existingCallable.getJavadocComment().orElse(null)));
        containingClassOrInterface.getMembers().replace(existingCallable, callableToReplaceWith);
    }
}
