/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.generator;

import com.github.javaparser.ParseResult;
import com.github.javaparser.Problem;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.io.IOException;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.github.javaparser.ast.NodeList.toNodeList;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * A general pattern that the generators in this module will follow.
 */
public abstract class AbstractGenerator {

    protected static final String COPYRIGHT_NOTICE_JP_CORE = "\n" +
            " * Copyright (C) 2007-2010 Júlio Vilmar Gesser.\n" +
            " * Copyright (C) 2011, 2013-2023 The JavaParser Team.\n" +
            " *\n" +
            " * This file is part of JavaParser.\n" +
            " *\n" +
            " * JavaParser can be used either under the terms of\n" +
            " * a) the GNU Lesser General Public License as published by\n" +
            " *     the Free Software Foundation, either version 3 of the License, or\n" +
            " *     (at your option) any later version.\n" +
            " * b) the terms of the Apache License\n" +
            " *\n" +
            " * You should have received a copy of both licenses in LICENCE.LGPL and\n" +
            " * LICENCE.APACHE. Please refer to those files for details.\n" +
            " *\n" +
            " * JavaParser is distributed in the hope that it will be useful,\n" +
            " * but WITHOUT ANY WARRANTY; without even the implied warranty of\n" +
            " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n" +
            " * GNU Lesser General Public License for more details.\n" +
            " ";

    protected static final String COPYRIGHT_NOTICE_JP_SS = "\n" +
            " * Copyright (C) 2015-2016 Federico Tomassetti\n" +
            " * Copyright (C) 2017-2023 The JavaParser Team.\n" +
            " *\n" +
            " * This file is part of JavaParser.\n" +
            " *\n" +
            " * JavaParser can be used either under the terms of\n" +
            " * a) the GNU Lesser General Public License as published by\n" +
            " *     the Free Software Foundation, either version 3 of the License, or\n" +
            " *     (at your option) any later version.\n" +
            " * b) the terms of the Apache License\n" +
            " *\n" +
            " * You should have received a copy of both licenses in LICENCE.LGPL and\n" +
            " * LICENCE.APACHE. Please refer to those files for details.\n" +
            " *\n" +
            " * JavaParser is distributed in the hope that it will be useful,\n" +
            " * but WITHOUT ANY WARRANTY; without even the implied warranty of\n" +
            " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n" +
            " * GNU Lesser General Public License for more details.\n" +
            " ";

    protected final SourceRoot sourceRoot;

    protected AbstractGenerator(SourceRoot sourceRoot) {
        this.sourceRoot = sourceRoot;
    }

    private void addOrReplaceMethod(
            ClassOrInterfaceDeclaration containingClassOrInterface,
            CallableDeclaration<?> callable,
            Runnable onNoExistingMethod
    ) {
        List<CallableDeclaration<?>> existingMatchingCallables = containingClassOrInterface.getCallablesWithSignature(callable.getSignature());
        if (existingMatchingCallables.isEmpty()) {
            // A matching callable exists -- will now normally add/insert.
            onNoExistingMethod.run();
        } else {
            // A matching callable doe NOT exist -- will now normally replace.
            if (existingMatchingCallables.size() > 1) {
                throw new AssertionError(f("Wanted to regenerate a method with signature %s in %s, but found more than one, and unable to disambiguate.", callable.getSignature(), containingClassOrInterface.getNameAsString()));
            }

            final CallableDeclaration<?> existingCallable = existingMatchingCallables.get(0);

            // Attempt to retain any existing javadoc.

            // TODO: Confirm what is done with normal comments...
            Optional<JavadocComment> callableJavadocComment = callable.getJavadocComment();
            Optional<JavadocComment> existingCallableJavadocComment = existingCallable.getJavadocComment();

            Optional<Comment> callableComment = callable.getComment();
            Optional<Comment> existingCallableComment = existingCallable.getComment();

            callable.setComment(callableComment.orElse(existingCallable.getComment().orElse(null)));
//            callable.setJavadocComment(callableJavadocComment.orElse(existingCallableJavadocComment.orElse(null)));

            // Mark the method as having been fully/partially generated.
            annotateGenerated(callable);

            if (callable.isMethodDeclaration()) {
                // We want the methods that we generate/insert to be pretty printed.
                MethodDeclaration prettyMethodDeclaration = prettyPrint(callable.asMethodDeclaration(), "    ");

                // Do the replacement.
                containingClassOrInterface.getMembers().replace(existingCallable, prettyMethodDeclaration);
            } else {
                // TODO: Unable to parse a constructor directly...?

                // Do the replacement.
                containingClassOrInterface.getMembers().replace(existingCallable, callable);
            }
        }
    }

    /**
     * Utility method that looks for a method or constructor with an identical signature as "callable" and replaces it
     * with callable. If not found, adds callable. When the new callable has no javadoc, any old javadoc will be kept.
     */
    protected void addOrReplaceWhenSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        addOrReplaceMethod(
                containingClassOrInterface,
                callable,
                () -> {
                    annotateGenerated(callable);
                    containingClassOrInterface.addMember(callable);
                }
        );
    }

    protected void after() throws Exception {
    }

    /**
     * @param node       The node to which the annotation will be added.
     * @param annotation The annotation to be added to the given node.
     * @param content    Where an annotation has content, it is passed here (otherwise null).
     * @param <T>        Only accept nodes which accept annotations.
     */
    private <T extends NodeWithAnnotations<?>> void annotate(T node, Class<?> annotation, Expression content) {
        NodeList<AnnotationExpr> annotations = node.getAnnotations()
                .stream()
                .filter(a -> !a.getNameAsString().equals(annotation.getSimpleName()))
                .collect(toNodeList());

        node.setAnnotations(annotations);

        if (content != null) {
            node.addSingleMemberAnnotation(annotation.getSimpleName(), content);
        } else {
            node.addMarkerAnnotation(annotation.getSimpleName());
        }

        // The annotation class will normally need to be imported.
        node.tryAddImportToParentCompilationUnit(annotation);
    }

    /**
     * @param node The node to which the {@code @Annotated} annotation will be added.
     * @param <T>
     */
    protected <T extends Node & NodeWithAnnotations<?>> void annotateGenerated(T node) {
        annotate(node, Generated.class, new StringLiteralExpr(getClass().getName()));
    }

    protected <T extends Node & NodeWithAnnotations<?>> void removeAnnotation(T node, Class<?> annotation) {
        node.getAnnotations().removeIf(annotationExpr ->
                annotationExpr.getName().asString().equals(
                        annotation.getSimpleName()
                )
        );

        node.findAncestor(CompilationUnit.class).ifPresent(compilationUnit -> {
            removeAnnotationImportIfUnused(compilationUnit, annotation);
        });

    }

    protected <T extends Node & NodeWithAnnotations<?>> void removeGenerated(T node) {
        removeAnnotation(node, Generated.class);
    }

    protected void removeAnnotationImportIfUnused(CompilationUnit compilationUnit, Class<?> annotation) {

        List<AnnotationExpr> staleAnnotations = compilationUnit
                .findAll(AnnotationExpr.class)
                .stream()
                .filter(annotationExpr ->
                        annotationExpr.getName().asString().equals(
                                annotation.getSimpleName()
                        )
                )
                .collect(Collectors.toList());

        if (staleAnnotations.isEmpty()) {
            // If there are no usages of this annotation, remove the import.
            boolean isRemoved = compilationUnit.getImports().removeIf(importDeclaration -> {
                return importDeclaration.getNameAsString().equals(annotation.getCanonicalName());
            });
        }
    }

    /**
     * @param method The node to which the {@code @Override} annotation will be added.
     */
    protected void annotateOverridden(MethodDeclaration method) {
        annotate(method, Override.class, null);
    }

    /**
     * @param node The node to which the {@code @SuppressWarnings} annotation will be added.
     * @param <T>  Only accept nodes which accept annotations.
     */
    protected <T extends NodeWithAnnotations<?>> void annotateSuppressWarnings(T node, String warningType) {
        annotate(node, SuppressWarnings.class, new StringLiteralExpr(warningType));
    }

    /**
     * Removes all methods from containingClassOrInterface that have the same signature as callable.
     * This is not currently used directly by any current generators, but may be useful when changing a generator
     * and you need to get rid of a set of outdated methods.
     */
    protected void removeMethodWithSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        for (CallableDeclaration<?> existingCallable : containingClassOrInterface.getCallablesWithSignature(callable.getSignature())) {
            containingClassOrInterface.remove(existingCallable);
        }
    }

    /**
     * Utility method that looks for a method or constructor with an identical signature as "callable" and replaces it
     * with callable. If not found, fails. When the new callable has no javadoc, any old javadoc will be kept. The
     * method or constructor is annotated with the generator class.
     */
    protected void replaceWhenSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        addOrReplaceMethod(
                containingClassOrInterface,
                callable,
                () -> {
                    throw new AssertionError(f("Wanted to regenerate a method with signature %s in %s, but it wasn't there.", callable.getSignature(), containingClassOrInterface.getNameAsString()));
                }
        );
    }


    protected List<CompilationUnit> getParsedCompilationUnitsFromSourceRoot(SourceRoot sourceRoot) throws IOException {
        List<CompilationUnit> cus = sourceRoot.getCompilationUnits();
        List<ParseResult<CompilationUnit>> parseResults = sourceRoot.tryToParse();

        boolean allParsed = parseResults.stream().allMatch(ParseResult::isSuccessful);
        if (!allParsed) {
            List<ParseResult<CompilationUnit>> problemResults = parseResults.stream().filter(compilationUnitParseResult -> !compilationUnitParseResult.isSuccessful()).collect(Collectors.toList());
            for (int i = 0; i < problemResults.size(); i++) {
                ParseResult<CompilationUnit> parseResult = problemResults.get(i);
                List<Problem> problems = parseResult.getProblems();
                Log.info("");
                Log.info("Problems (" + (i + 1) + " of " + problemResults.size() + "): ");
                Log.info(problems.toString());
            }

            throw new IllegalStateException("Expected all files to parse.");
        }

        Log.info("parseResults.size() = " + parseResults.size());

        return parseResults.stream()
                .map(ParseResult::getResult)
                .map(Optional::get)
                .collect(Collectors.toList());
    }


    protected MethodDeclaration prettyPrint(MethodDeclaration methodDeclaration) {
        return prettyPrint(methodDeclaration, "");
    }
    protected MethodDeclaration prettyPrint(MethodDeclaration methodDeclaration, String indent) {
        String methodDeclarationString = indent + methodDeclaration.toString().replaceAll("(\\R)", "$1" + indent);
        MethodDeclaration prettyMethodDeclaration = StaticJavaParser.parseMethodDeclaration(methodDeclarationString);

        return prettyMethodDeclaration;
    }

    protected EnumDeclaration prettyPrint(EnumDeclaration enumDeclaration) {
        return prettyPrint(enumDeclaration, "");
    }
    protected EnumDeclaration prettyPrint(EnumDeclaration enumDeclaration, String indent) {
        String enumDeclarationString = indent + enumDeclaration.toString().replaceAll("(\\R)", "$1" + indent);
        TypeDeclaration<?> prettyEnumDeclaration = StaticJavaParser.parseTypeDeclaration(enumDeclarationString);

        LexicalPreservingPrinter.setup(prettyEnumDeclaration);

        // We know that it is an enum declaration.
        return prettyEnumDeclaration.asEnumDeclaration();
    }

    protected SwitchStmt prettyPrint(SwitchStmt switchStmt) {
        return prettyPrint(switchStmt, "");
    }
    protected SwitchStmt prettyPrint(SwitchStmt switchStmt, String indent) {
        String switchStmtString = indent + switchStmt.toString().replaceAll("(\\R)", "$1" + indent);
        Statement prettySwitchStmt = StaticJavaParser.parseStatement(switchStmtString);

        LexicalPreservingPrinter.setup(prettySwitchStmt);

        // We know that it is an switch statement.
        return prettySwitchStmt.asSwitchStmt();
    }
}
