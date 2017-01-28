package com.github.javaparser.generator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

import java.io.IOException;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;

public abstract class NodeGenerator extends Generator {
    protected NodeGenerator(JavaParser javaParser, SourceRoot sourceRoot, JavaParserMetaModel javaParserMetaModel) {
        super(javaParser, sourceRoot, javaParserMetaModel);
    }

    public final void generate() throws IOException {
        for (BaseNodeMetaModel nodeMetaModel : javaParserMetaModel.getNodeMetaModels()) {
            CompilationUnit nodeCu = sourceRoot.parse(nodeMetaModel.getPackageName(), nodeMetaModel.getTypeName() + ".java", javaParser).orElseThrow(() -> new IOException(f("java file for %s not found", nodeMetaModel.getTypeName())));
            ClassOrInterfaceDeclaration nodeCoid = nodeCu.getClassByName(nodeMetaModel.getTypeName()).orElseThrow(() -> new IOException("Can't find class"));
            generateNode(nodeMetaModel, nodeCu, nodeCoid);
        }
    }

    protected abstract void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid);
}
