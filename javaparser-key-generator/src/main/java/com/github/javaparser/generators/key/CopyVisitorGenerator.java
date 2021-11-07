package com.github.javaparser.generators.key;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.*;
import com.github.javaparser.generator.Generator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;
import java.util.Set;
import java.util.TreeSet;

import static com.github.javaparser.generators.key.CopyNodeGenerator.*;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class CopyVisitorGenerator extends Generator {
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
    };
    private final Path output;

    public CopyVisitorGenerator(SourceRoot sourceRoot, Path outputDirectory) {
        super(sourceRoot);
        output = outputDirectory;

    }

    public final void generate() {
        Log.info("Running %s", () -> getClass().getSimpleName());
        for (var visitor : VISITORS) {
            Pair<CompilationUnit, ClassOrInterfaceDeclaration> result = parseClass(visitor);
            generateNode(result.a, result.b);
        }
    }


    protected Pair<CompilationUnit, ClassOrInterfaceDeclaration> parseClass(Class<?> fqn) {
        CompilationUnit nodeCu = sourceRoot.parse(fqn.getPackageName(), fqn.getSimpleName() + ".java")
                .clone(); //Don't change the original file
        ClassOrInterfaceDeclaration nodeCoid = nodeCu.getClassByName(fqn.getSimpleName())
                .orElseThrow(() -> new AssertionError("Can't find class"));
        return new Pair<>(nodeCu, nodeCoid);
    }

    private void generateNode(CompilationUnit cu, ClassOrInterfaceDeclaration visitor) {
        cu.setPackageDeclaration(CopyNodeGenerator.PACKAGE_VISITORS_NEW);
        cu.accept(new TypeRewriter(), null);
        rewriteVisitorImports(cu);
        rewriteNodeImports(cu);
        CopyNodeGenerator.write(cu, visitor.getFullyQualifiedName().get(), output);
    }


    private static void rewriteNodeImports(CompilationUnit cu) {
        for (ImportDeclaration anImport : cu.getImports()) {
            final var nameAsString = anImport.getNameAsString();
            if (nameAsString.startsWith(PACKAGE_NODE_OLD)) {
                anImport.setName(nameAsString.replace(PACKAGE_NODE_OLD, PACKAGE_NODE_NEW));
            }
        }
    }
}
