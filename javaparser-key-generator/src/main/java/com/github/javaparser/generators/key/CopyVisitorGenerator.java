package com.github.javaparser.generators.key;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.visitor.*;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class CopyVisitorGenerator extends ClassCopyGenerator {
    private static final Class<?>[] VISITORS = new Class<?>[]{
            ObjectIdentityHashCodeVisitor.class,
            HashCodeVisitor.class,
            GenericVisitorAdapter.class,
            ModifierVisitor.class,
            GenericListVisitorAdapter.class,
            EqualsVisitor.class,
            //DefaultVisitorAdapter.class,
            ObjectIdentityEqualsVisitor.class,
            NoCommentEqualsVisitor.class,
            NoCommentHashCodeVisitor.class,
            CloneVisitor.class,
            GenericVisitorWithDefaults.class,
            GenericVisitor.class,
            Visitable.class,
            VoidVisitor.class};

    public CopyVisitorGenerator(SourceRoot sourceRoot, Path outputDirectory) {
        super(sourceRoot, outputDirectory, VISITORS);

    }

    protected void generateClass(CompilationUnit cu, ClassOrInterfaceDeclaration visitor) {
        cu.setPackageDeclaration(Transformers.PACKAGE_VISITORS_NEW);
        cu.accept(new TypeRewriter(), null);
        Transformers.rewriteVisitorImports(cu);
        rewriteNodeImports(cu);
        Transformers.write(cu, visitor.getFullyQualifiedName().get(), output);
    }


    private static void rewriteNodeImports(CompilationUnit cu) {
        for (ImportDeclaration anImport : cu.getImports()) {
            final var nameAsString = anImport.getNameAsString();
            if (nameAsString.startsWith(Transformers.PACKAGE_NODE_OLD)) {
                anImport.setName(nameAsString.replace(Transformers.PACKAGE_NODE_OLD, Transformers.PACKAGE_NODE_NEW));
            }
        }
    }
}
