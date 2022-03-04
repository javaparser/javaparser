package com.github.javaparser.generators.key;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.generator.Generator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;

import static com.github.javaparser.generators.key.Transformers.*;


/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class CopyNodeGenerator extends Generator {


    private final Path output;

    protected CopyNodeGenerator(SourceRoot sourceRoot, Path outputDirectory) {
        super(sourceRoot);
        this.output = outputDirectory;
    }

    public final void generate() {
        Log.info("Running %s", () -> getClass().getSimpleName());
        for (BaseNodeMetaModel nodeMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            Pair<CompilationUnit, ClassOrInterfaceDeclaration> result = parseNode(nodeMetaModel);
            generateNode(nodeMetaModel, result.a, result.b);
        }
    }

    protected Pair<CompilationUnit, ClassOrInterfaceDeclaration> parseNode(BaseNodeMetaModel nodeMetaModel) {
        CompilationUnit nodeCu =
                sourceRoot.parse(nodeMetaModel.getPackageName(), nodeMetaModel.getTypeName() + ".java")
                        .clone(); //Don't change the original file
        ClassOrInterfaceDeclaration nodeCoid = nodeCu.getClassByName(nodeMetaModel.getTypeName()).orElseThrow(() -> new AssertionError("Can't find class"));
        return new Pair<>(nodeCu, nodeCoid);
    }


    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        allFieldsAreFinal(nodeCoid);
        removeObservable(nodeCu, nodeCoid);
        rewriteVisitorImports(nodeCu);
        rewritePackage(nodeCu);
        rewriteImplements(nodeCoid);

        Transformers.rewriteConstructors(nodeCoid);

        changeVisibility(nodeCoid, Modifier.Keyword.PRIVATE, name -> name.startsWith("set"));
        changeVisibility(nodeCoid, Modifier.Keyword.PROTECTED, name ->
                name.startsWith("setParentNode") || name.startsWith("setAsParentNodeOf"));
        removeUnwantedMethods(nodeCoid, name ->
                name.startsWith("add") || name.startsWith("remove")
                        || name.startsWith("replace"));

        removeUnwantedFields(nodeCoid, this::isUnwantedField);
        nodeCu.accept(new TypeRewriter(), null);
        addImports(nodeCu);
        nodeCoid.setName("I" + nodeCoid.getNameAsString());

        nodeCoid.getFullyQualifiedName().ifPresent(it -> write(nodeCu, it));
    }

    private boolean isUnwantedField(String s) {
        switch (s) {
            case "associatedSpecificationComments":
            case "comment":
            case "orphanComments":
            case "observers":
            case "parsed":
                return true;
            default:
                return false;
        }
    }

    private void removeObservable(CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        //nodeCu.getImports().removeIf(it -> it.getNameAsString().startsWith("Observable"));
        //nodeCoid.getImplementedTypes().removeIf(it ->
        //        it.getNameAsString().startsWith("Observable"));
    }

    public void write(CompilationUnit nodeCu, String fullyQualifiedName) {
        Transformers.write(nodeCu, fullyQualifiedName, output);
    }

    private void allFieldsAreFinal(ClassOrInterfaceDeclaration nodeCoid) {
        //for (FieldDeclaration field : nodeCoid.getFields()) {
        //    field.addModifier(Modifier.Keyword.FINAL);
        //}
    }

    public static void rewriteImplements(ClassOrInterfaceDeclaration nodeCoid) {
        for (ClassOrInterfaceType implementedType : nodeCoid.getImplementedTypes()) {
            var s = implementedType.getNameAsString();
            if (s.startsWith("NodeWith") || "HasParentNode".equals(s)) {
                implementedType.setName("I" + s);
            }
        }
    }
}
