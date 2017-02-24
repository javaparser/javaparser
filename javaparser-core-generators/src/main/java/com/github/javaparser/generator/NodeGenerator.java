package com.github.javaparser.generator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.io.IOException;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Makes it easier to generate code in the core AST nodes. The generateNode method will get every node type passed to
 * it, ready for modification.
 */
public abstract class NodeGenerator extends Generator {
    protected NodeGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    public final void generate() throws Exception {
        Log.info("Running %s", getClass().getSimpleName());
        for (BaseNodeMetaModel nodeMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            CompilationUnit nodeCu = sourceRoot.parse(nodeMetaModel.getPackageName(), nodeMetaModel.getTypeName() + ".java");
            ClassOrInterfaceDeclaration nodeCoid = nodeCu.getClassByName(nodeMetaModel.getTypeName()).orElseThrow(() -> new IOException("Can't find class"));
            generateNode(nodeMetaModel, nodeCu, nodeCoid);
        }
        after();
    }

    protected void after() throws Exception {

    }

    protected abstract void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid);
}
