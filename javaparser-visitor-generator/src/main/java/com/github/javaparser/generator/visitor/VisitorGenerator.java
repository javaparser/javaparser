package com.github.javaparser.generator.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

import java.io.IOException;
import java.util.Optional;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;

public abstract class VisitorGenerator {
    protected final JavaParser javaParser;
    protected final SourceRoot sourceRoot;
    private final String pkg;
    private final String visitorClassName;
    protected final JavaParserMetaModel javaParserMetaModel;

    public VisitorGenerator(JavaParser javaParser, SourceRoot sourceRoot, String pkg, String visitorClassName, JavaParserMetaModel javaParserMetaModel) {
        this.javaParser = javaParser;
        this.sourceRoot = sourceRoot;
        this.pkg = pkg;
        this.visitorClassName = visitorClassName;
        this.javaParserMetaModel = javaParserMetaModel;
    }

    public void generate() throws IOException {
        CompilationUnit voidVisitorCu = sourceRoot.parse(pkg, visitorClassName + ".java", javaParser).get();

        Optional<ClassOrInterfaceDeclaration> visitorClassOptional = voidVisitorCu.getClassByName(visitorClassName);
        if (!visitorClassOptional.isPresent()) {
            visitorClassOptional = voidVisitorCu.getInterfaceByName(visitorClassName);
        }
        ClassOrInterfaceDeclaration visitorClass = visitorClassOptional.get();

        for (BaseNodeMetaModel node : javaParserMetaModel.getNodeMetaModels()) {
            if (!node.isAbstract()) {
                Optional<MethodDeclaration> visitMethod = visitorClass.getMethods().stream()
                        .filter(m -> m.getNameAsString().equals("visit"))
                        .filter(m -> m.getParameter(0).getType().toString().equals(node.getTypeName()))
                        .findFirst();
                visitMethod.ifPresent(m -> generateVisitorFor(node, m, voidVisitorCu));
                if (!visitMethod.isPresent()) {
                    System.out.println(f("No visit method found for type %s", node));
                }
            }
        }
    }

    protected abstract void generateVisitorFor(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit voidVisitorCu);
}
