package com.github.javaparser.generators.key;

import com.github.javaparser.HasParentNode;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.nodeTypes.modifiers.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;

import static com.github.javaparser.generators.key.Transformers.*;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class CopyInterfacesGenerator extends ClassCopyGenerator {
    public static final Class<?>[] INTERFACES = new Class[]{
            NodeWithAbstractModifier.class,
            NodeWithAccessModifiers.class,
            NodeWithFinalModifier.class,
            NodeWithPrivateModifier.class,
            NodeWithProtectedModifier.class,
            NodeWithPublicModifier.class,
            NodeWithStaticModifier.class,
            NodeWithStrictfpModifier.class,
            NodeWithAnnotations.class,
            NodeWithArguments.class,
            NodeWithBlockStmt.class,
            NodeWithBody.class,
            NodeWithCondition.class,
            NodeWithDeclaration.class,
            NodeWithExpression.class,
            NodeWithExtends.class,
            NodeWithIdentifier.class,
            NodeWithImplements.class,
            NodeWithJavadoc.class,
            NodeWithMembers.class,
            NodeWithModifiers.class,
            HasParentNode.class,
            NodeWithName.class,
            NodeWithOptionalBlockStmt.class,
            NodeWithOptionalLabel.class,
            NodeWithOptionalScope.class,
            NodeWithParameters.class,
            NodeWithRange.class,
            NodeWithScope.class,
            NodeWithSimpleName.class,
            NodeWithStatements.class,
            NodeWithThrownExceptions.class,
            NodeWithTokenRange.class,
            NodeWithTraversableScope.class,
            NodeWithType.class,
            NodeWithTypeArguments.class,
            NodeWithTypeParameters.class,
            NodeWithVariables.class,
            SwitchNode.class
    };

    private final Path output;

    public CopyInterfacesGenerator(SourceRoot sourceRoot, Path outputDirectory) {
        super(sourceRoot, outputDirectory, INTERFACES);
        this.output = outputDirectory;
    }

    @Override
    protected void generateClass(CompilationUnit unit, ClassOrInterfaceDeclaration type) {
        rewriteTypes(unit);
        rewriteVisitorImports(unit);
        rewritePackage(unit);
        removeUnwantedMethods(type, it -> it.startsWith("set") || it.startsWith("add") || it.startsWith("tryAdd"));
        rewriteExtends(type);
        type.setName("I" + type.getNameAsString());
        write(unit, type.getFullyQualifiedName().get(), output);
    }

    public static void rewriteExtends(ClassOrInterfaceDeclaration nodeCoid) {
        for (ClassOrInterfaceType implementedType : nodeCoid.getExtendedTypes()) {
            var s = implementedType.asString();
            if (s.startsWith("NodeWith")) {
                implementedType.setName("I" + s);
            }
        }
    }
}
