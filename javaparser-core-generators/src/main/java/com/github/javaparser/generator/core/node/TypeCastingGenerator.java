package com.github.javaparser.generator.core.node;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.SourceRoot;

import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.set;

public class TypeCastingGenerator extends NodeGenerator {
    private final Set<BaseNodeMetaModel> baseNodes = set(
            JavaParserMetaModel.statementMetaModel,
            JavaParserMetaModel.expressionMetaModel,
            JavaParserMetaModel.typeMetaModel,
            JavaParserMetaModel.moduleDirectiveMetaModel,
            JavaParserMetaModel.bodyDeclarationMetaModel,
            JavaParserMetaModel.commentMetaModel
    );

    public TypeCastingGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) throws Exception {
        Pair<CompilationUnit, ClassOrInterfaceDeclaration> baseCode = null;
        for (BaseNodeMetaModel baseNode : baseNodes) {
            if(nodeMetaModel == baseNode) {
                // We adjust the base models from the child nodes,
                // so we don't do anything when we *are* the base model.
                return;
            }
            if (nodeMetaModel.isInstanceOfMetaModel(baseNode)) {
                baseCode = parseNode(baseNode);
            }
        }

        if (baseCode == null) {
            // Node is not a child of one of the base nodes, so we don't want to generate this method for it.
            return;
        }

        final String typeName = nodeMetaModel.getTypeName();
        final ClassOrInterfaceDeclaration baseCoid = baseCode.b;
        final CompilationUnit baseCu = baseCode.a;
        
        generateIsType(baseCu, nodeCoid, baseCoid, typeName);
        generateAsType(baseCu, nodeCoid, baseCoid, typeName);
        generateToType(nodeCu, baseCu, nodeCoid, baseCoid, typeName);
        generateIfType(nodeCu, baseCu, nodeCoid, baseCoid, typeName);
    }

    private void generateAsType(CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        final MethodDeclaration asTypeBaseMethod = (MethodDeclaration) parseBodyDeclaration(f("public %s as%s() { throw new IllegalStateException(f(\"%%s is not an %s\", this)); }", typeName, typeName, typeName));
        final MethodDeclaration asTypeNodeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public %s as%s() { return this; }", typeName, typeName));
        addOrReplaceWhenSameSignature(baseCoid, asTypeBaseMethod);
        addOrReplaceWhenSameSignature(nodeCoid, asTypeNodeMethod);
        baseCu.addImport("com.github.javaparser.utils.CodeGenerationUtils.f", true, false);
    }

    private void generateToType(CompilationUnit nodeCu, CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        baseCu.addImport(Optional.class);
        nodeCu.addImport(Optional.class);
        final MethodDeclaration asTypeBaseMethod = (MethodDeclaration) parseBodyDeclaration(f("public Optional<%s> to%s() { return Optional.empty(); }", typeName, typeName, typeName));
        final MethodDeclaration asTypeNodeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public Optional<%s> to%s() { return Optional.of(this); }", typeName, typeName));
        addOrReplaceWhenSameSignature(baseCoid, asTypeBaseMethod);
        addOrReplaceWhenSameSignature(nodeCoid, asTypeNodeMethod);
    }

    private void generateIfType(CompilationUnit nodeCu, CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        final MethodDeclaration ifTypeBaseMethod = (MethodDeclaration) parseBodyDeclaration(f("public void if%s(Consumer<%s> action) { }", typeName, typeName));
        final MethodDeclaration ifTypeNodeMethod = (MethodDeclaration) parseBodyDeclaration(f("public void if%s(Consumer<%s> action) { action.accept(this); }", typeName, typeName));
        addOrReplaceWhenSameSignature(baseCoid, ifTypeBaseMethod);
        addOrReplaceWhenSameSignature(nodeCoid, ifTypeNodeMethod);

        baseCu.addImport(Consumer.class);
        nodeCu.addImport(Consumer.class);
    }

    private void generateIsType(CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        final MethodDeclaration baseIsTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("public boolean is%s() { return false; }", typeName));
        final MethodDeclaration overriddenIsTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public boolean is%s() { return true; }", typeName));

        addOrReplaceWhenSameSignature(nodeCoid, overriddenIsTypeMethod);
        addOrReplaceWhenSameSignature(baseCoid, baseIsTypeMethod);
    }
}
