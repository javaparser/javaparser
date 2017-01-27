package com.github.javaparser.generator.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

/**
 * Generates JavaParser's GenericVisitor.
 */
public class GenericVisitorGenerator extends VisitorGenerator {
    GenericVisitorGenerator(JavaParser javaParser, SourceRoot sourceRoot, JavaParserMetaModel javaParserMetaModel) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "GenericVisitor", "R", "A", true, javaParserMetaModel);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, List<PropertyMetaModel> allPropertyMetaModels, CompilationUnit compilationUnit) {
        visitMethod.setBody(null);
    }
}
