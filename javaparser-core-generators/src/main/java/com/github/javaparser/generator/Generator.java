package com.github.javaparser.generator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.utils.SourceRoot;

import javax.annotation.Generated;
import java.util.List;

import static com.github.javaparser.ast.NodeList.toNodeList;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * A general pattern that the generators in this module will follow.
 */
public abstract class Generator {
    protected final SourceRoot sourceRoot;

    protected Generator(SourceRoot sourceRoot) {
        this.sourceRoot = sourceRoot;
    }

    public abstract void generate() throws Exception;

    protected <T extends Node & NodeWithAnnotations<?>> void annotateGenerated(T node) {
        annotate(node, Generated.class, new StringLiteralExpr(getClass().getName()));
    }

    protected <T extends Node & NodeWithAnnotations<?>> void annotateSuppressWarnings(T node) {
        annotate(node, SuppressWarnings.class, new StringLiteralExpr("unchecked"));
    }

    protected void annotateOverridden(MethodDeclaration method) {
        annotate(method, Override.class, null);
    }

    private <T extends Node & NodeWithAnnotations<?>> void annotate(T node, Class<?> annotation, Expression content) {
        node.setAnnotations(
                node.getAnnotations().stream()
                        .filter(a -> !a.getNameAsString().equals(annotation.getSimpleName()))
                        .collect(toNodeList()));

        if (content != null) {
            node.addSingleMemberAnnotation(annotation.getSimpleName(), content);
        } else {
            node.addMarkerAnnotation(annotation.getSimpleName());
        }
        node.tryAddImportToParentCompilationUnit(annotation);
    }

    /**
     * Utility method that looks for a method or constructor with an identical signature as "callable" and replaces it
     * with callable. If not found, adds callable. When the new callable has no javadoc, any old javadoc will be kept.
     */
    protected void addOrReplaceWhenSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        addMethod(containingClassOrInterface, callable, () -> containingClassOrInterface.addMember(callable));
    }

    /**
     * Utility method that looks for a method or constructor with an identical signature as "callable" and replaces it
     * with callable. If not found, fails. When the new callable has no javadoc, any old javadoc will be kept. The
     * method or constructor is annotated with the generator class.
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
        annotateGenerated(callable);
        containingClassOrInterface.getMembers().replace(existingCallable, callable);
    }

    /**
     * Removes all methods from containingClassOrInterface that have the same signature as callable. This is not used by
     * any code, but it is useful when changing a generator and you need to get rid of a set of outdated methods.
     */
    protected void removeMethodWithSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        for (CallableDeclaration<?> existingCallable : containingClassOrInterface.getCallablesWithSignature(callable.getSignature())) {
            containingClassOrInterface.remove(existingCallable);
        }
    }

}
