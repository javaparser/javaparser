package com.github.javaparser.generators.key;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;

import static com.github.javaparser.generators.key.Transformers.*;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class CopyNodeListGenerator extends ClassCopyGenerator {

    public CopyNodeListGenerator(SourceRoot sourceRoot, Path outputDirectory) {
        super(sourceRoot, outputDirectory, new Class[]{NodeList.class});
    }

    @Override
    protected void generateClass(CompilationUnit unit, ClassOrInterfaceDeclaration type) {
        rewriteTypes(unit);
        rewriteVisitorImports(unit);
        rewritePackage(unit);
        rewriteConstructors(type);
        removeUnwantedMethods(type, it -> it.startsWith("set") || it.startsWith("add") || it.startsWith("replace")
                || it.startsWith("sort")
                || it.startsWith("retain")
                || it.startsWith("clear"));
        type.setName("I" + type.getNameAsString());

        write(unit, type.getFullyQualifiedName().get(), output);
    }
}
