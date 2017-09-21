package com.github.javaparser.generator.core.node;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.SourceRoot;

import java.util.Set;
import java.util.function.Consumer;

import static com.github.javaparser.JavaParser.parseBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.set;

public class TypeCastingGenerator extends NodeGenerator {
    private final Set<BaseNodeMetaModel> baseNodes = set(
            JavaParserMetaModel.statementMetaModel,
            JavaParserMetaModel.expressionMetaModel,
            JavaParserMetaModel.typeMetaModel,
            JavaParserMetaModel.moduleStmtMetaModel,
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
        
        generateIsType(nodeCoid, baseCoid, typeName);
        generateAsType(baseCu, nodeCoid, baseCoid, typeName);
        generateIfType(baseCu, baseCoid, typeName);
    }

    private void generateAsType(CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        final MethodDeclaration asTypeBaseMethod = (MethodDeclaration) parseBodyDeclaration(f("public %s as%s() { throw new IllegalStateException(f(\"%%s is not an %s\", this)); }", typeName, typeName, typeName));
        final MethodDeclaration asTypeNodeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public %s as%s() { return this; }", typeName, typeName));
        addOrReplaceWhenSameSignature(baseCoid, asTypeBaseMethod);
        addOrReplaceWhenSameSignature(nodeCoid, asTypeNodeMethod);
        annotateGenerated(asTypeNodeMethod);
        annotateGenerated(asTypeBaseMethod);
        baseCu.addImport("com.github.javaparser.utils.CodeGenerationUtils.f", true, false);

    }

    private void generateIfType(CompilationUnit baseCu, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        final MethodDeclaration ifTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("public void if%s(Consumer<%s> action) { if (is%s()) { action.accept(as%s()); }}", typeName, typeName, typeName, typeName));

        addOrReplaceWhenSameSignature(baseCoid, ifTypeMethod);
        annotateGenerated(ifTypeMethod);

        baseCu.addImport(Consumer.class);
    }

    private void generateIsType(ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        final MethodDeclaration baseIsTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("public boolean is%s() { return false; }", typeName));
        final MethodDeclaration overriddenIsTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public boolean is%s() { return true; }", typeName));

        addOrReplaceWhenSameSignature(nodeCoid, overriddenIsTypeMethod);
        addOrReplaceWhenSameSignature(baseCoid, baseIsTypeMethod);

        annotateGenerated(overriddenIsTypeMethod);
        annotateGenerated(baseIsTypeMethod);
    }
}
