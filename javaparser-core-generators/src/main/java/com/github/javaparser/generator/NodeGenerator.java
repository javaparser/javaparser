package com.github.javaparser.generator;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.io.IOException;
import java.util.List;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Makes it easier to generate code in the core AST nodes. The generateNode method will get every node type passed to
 * it, ready for modification.
 */
public abstract class NodeGenerator extends Generator {
    protected NodeGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    public final void generate() throws Exception {
        Log.info("Running %s", getClass().getSimpleName());
        for (BaseNodeMetaModel nodeMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            CompilationUnit nodeCu = sourceRoot.parse(nodeMetaModel.getPackageName(), nodeMetaModel.getTypeName() + ".java");
            ClassOrInterfaceDeclaration nodeCoid = nodeCu.getClassByName(nodeMetaModel.getTypeName()).orElseThrow(() -> new IOException("Can't find class"));
            generateNode(nodeMetaModel, nodeCu, nodeCoid);
        }
        after();
    }

    protected void after() throws Exception {

    }

    protected abstract void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid);

    /**
     * Utility method that looks for a method or constructor with an identical signature as "callable" and replaces it
     * with callable. If not found, adds callable. When the new callable has no javadoc, any old javadoc will be kept.
     */
    protected void addOrReplaceWhenSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        addMethod(containingClassOrInterface, callable, () -> containingClassOrInterface.addMember(callable));
    }

    /**
     * Utility method that looks for a method or constructor with an identical signature as "callable" and replaces it
     * with callable. If not found, fails. When the new callable has no javadoc, any old javadoc will be kept.
     */
    protected void replaceWhenSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        addMethod(containingClassOrInterface, callable,
                () -> {
                    throw new AssertionError(f("Wanted to regenerate a method with signature %s in %s, but it wasn't there.", callable.getSignature(), containingClassOrInterface.getNameAsString()));
                });
    }

    private void addMethod(
            ClassOrInterfaceDeclaration containingClassOrInterface,
            CallableDeclaration<?> callable,
            Runnable onNoExistingMethod) {
        List<CallableDeclaration<?>> existingCallables = containingClassOrInterface.getCallablesWithSignature(callable.getSignature());
        if (existingCallables.isEmpty()) {
            onNoExistingMethod.run();
            return;
        }
        if (existingCallables.size() > 1) {
            throw new AssertionError(f("Wanted to regenerate a method with signature %s in %s, but found more than one.", callable.getSignature(), containingClassOrInterface.getNameAsString()));
        }
        final CallableDeclaration<?> existingCallable = existingCallables.get(0);
        callable.setJavadocComment(callable.getJavadocComment().orElse(existingCallable.getJavadocComment().orElse(null)));
        containingClassOrInterface.getMembers().replace(existingCallable, callable);
    }
}
