package com.github.javaparser.generator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;

/**
 * Makes it easier to generate code in the core AST nodes. The generateNode method will get every node type passed to it,
 * ready for modification.
 */
public abstract class NodeGenerator extends Generator {
    private final Logger log = LoggerFactory.getLogger(VisitorGenerator.class);

    protected NodeGenerator(JavaParser javaParser, SourceRoot sourceRoot) {
        super(javaParser, sourceRoot);
    }

    public final void generate() throws Exception {
        log.info(f("Running %s", getClass().getSimpleName()));
        for (BaseNodeMetaModel nodeMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            CompilationUnit nodeCu = sourceRoot.parse(nodeMetaModel.getPackageName(), nodeMetaModel.getTypeName() + ".java", javaParser);
            ClassOrInterfaceDeclaration nodeCoid = nodeCu.getClassByName(nodeMetaModel.getTypeName()).orElseThrow(() -> new IOException("Can't find class"));
            generateNode(nodeMetaModel, nodeCu, nodeCoid);
        }
        after();
    }

    protected void after() throws Exception {

    }

    protected abstract void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid);
}
