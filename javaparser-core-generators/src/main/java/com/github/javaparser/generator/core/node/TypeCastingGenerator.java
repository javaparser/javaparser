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

        // Generate the isType() method
        final String typeName = nodeMetaModel.getTypeName();
        final MethodDeclaration baseIsTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("public boolean is%s() { return false; }", typeName));
        final MethodDeclaration overriddenIsTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public boolean is%s() { return true; }", typeName));

        addOrReplaceWhenSameSignature(nodeCoid, overriddenIsTypeMethod);
        addOrReplaceWhenSameSignature(baseCode.b, baseIsTypeMethod);

        annotateGenerated(overriddenIsTypeMethod);
        annotateGenerated(baseIsTypeMethod);
        
        // Generate the asType() method
        final MethodDeclaration asTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("public %s as%s() { return (%s) this; }", typeName, typeName, typeName));
        addOrReplaceWhenSameSignature(baseCode.b, asTypeMethod);
        annotateGenerated(asTypeMethod);
        
        // Generate the ifType(Consumer) method
        final MethodDeclaration ifTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("public void if%s(Consumer<%s> action) { if (is%s()) { action.accept(as%s()); }}", typeName, typeName, typeName, typeName));
        
        addOrReplaceWhenSameSignature(baseCode.b, ifTypeMethod);
        annotateGenerated(ifTypeMethod);
        
        baseCode.a.addImport(Consumer.class);
    }
}
