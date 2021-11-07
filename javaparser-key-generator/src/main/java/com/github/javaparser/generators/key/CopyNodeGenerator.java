package com.github.javaparser.generators.key;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.generator.Generator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.SourceRoot;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;


/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class CopyNodeGenerator extends Generator {

    public static final String PACKAGE_VISITORS_OLD = "com.github.javaparser.ast.visitor";
    public static final String PACKAGE_VISITORS_NEW = "de.uka.ilkd.key.java.nast.visitor";

    public static final String PACKAGE_NODE_OLD = "com.github.javaparser.ast";
    public static final String PACKAGE_NODE_NEW = "de.uka.ilkd.key.java.nast";


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
        rewriteVisitorImports(nodeCu);
        nodeCu.accept(new TypeRewriter(), null);

        for (ConstructorDeclaration constructor : nodeCoid.getConstructors()) {
            constructor.setName("I" + constructor.getNameAsString());
        }

        List<MethodDeclaration> unwantedMethods = getUnwantedMethods(nodeCoid.getMethods());
        nodeCoid.getMembers().removeAll(unwantedMethods);
        nodeCoid.setName("I" + nodeCoid.getNameAsString());
        nodeCu.setPackageDeclaration(
                nodeCu.getPackageDeclaration().get().getNameAsString()
                        .replace(PACKAGE_NODE_OLD,PACKAGE_NODE_NEW));
        nodeCoid.getFullyQualifiedName().ifPresent(it -> write(nodeCu, it));
    }

    public void write(CompilationUnit nodeCu, String fullyQualifiedName) {
        write(nodeCu, fullyQualifiedName, output);
    }

    public static void write(CompilationUnit nodeCu, String fullyQualifiedName, Path output) {
        String filepath = fullyQualifiedName.replace('.', '/') + ".java";
        Path p = output.resolve(filepath);
        try {
            Files.createDirectories(p.getParent());
            Files.writeString(p, nodeCu.toString());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void allFieldsAreFinal(ClassOrInterfaceDeclaration nodeCoid) {
        for (FieldDeclaration field : nodeCoid.getFields()) {
            field.addModifier(Modifier.Keyword.FINAL);
        }
    }

    public static void rewriteVisitorImports(CompilationUnit nodeCu) {
        for (ImportDeclaration anImport : nodeCu.getImports()) {
            final var nameAsString = anImport.getNameAsString();
            if (nameAsString.startsWith(PACKAGE_VISITORS_OLD)) {
                anImport.setName(nameAsString.replace(PACKAGE_VISITORS_OLD, PACKAGE_VISITORS_NEW));
            }
        }
    }

    private List<MethodDeclaration> getUnwantedMethods(List<MethodDeclaration> methods) {
        return methods.stream().filter(it -> unwanted(it.getNameAsString())).collect(Collectors.toList());
    }

    private boolean unwanted(String name) {
        return name.startsWith("set") || name.startsWith("add") || name.startsWith("remove")
                || name.startsWith("replace");
    }
}
