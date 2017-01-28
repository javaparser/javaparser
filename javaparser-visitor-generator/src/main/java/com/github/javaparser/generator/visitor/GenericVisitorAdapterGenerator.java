package com.github.javaparser.generator.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import java.util.List;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;

/**
 * Generates JavaParser's VoidVisitorAdapter.
 */
public class GenericVisitorAdapterGenerator extends VisitorGenerator {
    GenericVisitorAdapterGenerator(JavaParser javaParser, SourceRoot sourceRoot, JavaParserMetaModel javaParserMetaModel) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "GenericVisitorAdapter", "void", "A", true, javaParserMetaModel);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, List<PropertyMetaModel> allPropertyMetaModels, CompilationUnit compilationUnit) {
        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();
        
        body.addStatement("R result;");

        final String resultCheck = "if (result != null) return result;";

        for (PropertyMetaModel field : allPropertyMetaModels) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isOptional()) {
                    body.addStatement(f("if (n.%s.isPresent()) {" +
                            "   result = n.%s.get().accept(this, arg);" +
                            "   %s" +
                            "}", getter, getter, resultCheck));
                } else {
                    body.addStatement(f("{ result = n.%s.accept(this, arg); %s }", getter, resultCheck));
                }
            }
        }
        body.addStatement("return null;");
    }
}
