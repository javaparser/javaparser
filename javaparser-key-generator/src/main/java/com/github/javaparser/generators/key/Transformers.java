package com.github.javaparser.generators.key;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedList;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class Transformers {

    public static final String PACKAGE_VISITORS_OLD = "com.github.javaparser.ast.visitor";
    public static final String PACKAGE_VISITORS_NEW = "de.uka.ilkd.key.java.nast.visitor";
    public static final String PACKAGE_NODE_OLD = "com.github.javaparser.ast";
    public static final String PACKAGE_NODE_NEW = "de.uka.ilkd.key.java.nast";

    public static void removeUnwantedFields(ClassOrInterfaceDeclaration type, Predicate<String> unwanted) {
        var fields = type.getFields();
        var seq = new LinkedList<FieldDeclaration>();
        for (FieldDeclaration field : fields) {
            field.getVariables().removeIf(it -> unwanted.test(it.getNameAsString()));
            if (field.getVariables().isEmpty()) {
                seq.add(field);
            }
        }
        type.getMembers().removeAll(seq);
    }

    public static void changeVisibility(ClassOrInterfaceDeclaration type, Modifier.Keyword newVisibility,
                                        Predicate<String> pred) {
        for (MethodDeclaration method : type.getMethods()) {
            if (pred.test(method.getNameAsString())) {
                method.removeModifier(Modifier.Keyword.PUBLIC, Modifier.Keyword.PRIVATE, Modifier.Keyword.PROTECTED);
                if (newVisibility != null)
                    method.addModifier(newVisibility);
            }
        }
    }

    public static void removeUnwantedMethods(ClassOrInterfaceDeclaration type, Predicate<String> unwanted) {
        var methods = type.getMethods();
        var u = methods.stream().filter(it -> unwanted.test(it.getNameAsString()))
                .collect(Collectors.toList());
        type.getMembers().removeAll(u);
    }

    public static boolean unwanted(String name) {
        return name.startsWith("set") || name.startsWith("add") || name.startsWith("remove")
                || name.startsWith("replace");
    }

    public static void rewriteVisitorImports(CompilationUnit nodeCu) {
        for (ImportDeclaration anImport : nodeCu.getImports()) {
            final var nameAsString = anImport.getNameAsString();
            if (nameAsString.startsWith(PACKAGE_NODE_OLD)
                    && TypeRewriter.NODE_TYPES.contains(anImport.getName().getIdentifier())) {
                anImport.setName(
                        nameAsString.replace(PACKAGE_NODE_OLD, PACKAGE_NODE_NEW)
                                .replace(anImport.getName().getIdentifier(),
                                        "I" + anImport.getName().getIdentifier()));
            }

            if (nameAsString.startsWith(PACKAGE_VISITORS_OLD)) {
                anImport.setName(nameAsString.replace(PACKAGE_VISITORS_OLD, PACKAGE_VISITORS_NEW));
            }
        }

    }

    public static void addImports(CompilationUnit unit) {
        unit.addImport("com.github.javaparser.ast.Generated");
        unit.addImport("com.github.javaparser.ast.AllFieldsConstructor");
        unit.addImport("de.uka.ilkd.key.java.nast.nodeTypes.*");
        unit.addImport("de.uka.ilkd.key.java.nast.*");
    }

    public static void rewriteTypes(CompilationUnit unit) {
        unit.accept(new TypeRewriter(), null);
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

    public static void rewritePackage(CompilationUnit unit) {
        unit.setPackageDeclaration(
                unit.getPackageDeclaration().get().getNameAsString()
                        .replace(PACKAGE_NODE_OLD, PACKAGE_NODE_NEW));
    }

    public static void rewriteConstructors(ClassOrInterfaceDeclaration unit) {
        for (ConstructorDeclaration constructor : unit.getConstructors()) {
            constructor.setName("I" + constructor.getNameAsString());
        }
    }
}
