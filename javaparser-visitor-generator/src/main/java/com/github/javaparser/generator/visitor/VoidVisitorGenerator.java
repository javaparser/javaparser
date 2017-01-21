package com.github.javaparser.generator.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

public class VoidVisitorGenerator extends VisitorGenerator {
    public VoidVisitorGenerator(JavaParser javaParser, SourceRoot sourceRoot, JavaParserMetaModel javaParserMetaModel) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "VoidVisitor", javaParserMetaModel);
    }

    @Override
    protected void generateVisitorFor(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit voidVisitorCu) {
        visitMethod.setBody(null);
    }
}
