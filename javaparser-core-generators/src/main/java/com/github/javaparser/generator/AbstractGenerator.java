/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.generator.core.CoreGenerator;
import com.github.javaparser.utils.SourceRoot;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.github.javaparser.ast.NodeList.toNodeList;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * A general pattern that the generators in this module will follow.
 */
public abstract class AbstractGenerator {

    public static final String COPYRIGHT_NOTICE_JP_CORE = "\n" +
            " * Copyright (C) 2007-2010 Júlio Vilmar Gesser.\n" +
            " * Copyright (C) 2011, 2013-2020 The JavaParser Team.\n" +
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

    public static final String COPYRIGHT_NOTICE_JP_SS = "\n" +
            " * Copyright (C) 2015-2016 Federico Tomassetti\n" +
            " * Copyright (C) 2017-2020 The JavaParser Team.\n" +
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
    protected List<CompilationUnit> editedCus;

    /**
     * @param sourceRoot The base directory from which java files (and packages) will be resolved against.
     */
    protected AbstractGenerator(SourceRoot sourceRoot) {
        this.sourceRoot = sourceRoot;
        this.editedCus = new ArrayList<>();
    }

    protected void before() {
        // Default: Empty / no-operation.
    }

    protected void after() {
        // Default: Empty / no-operation.
    }

    /**
     * @return A list of compilation units that have been modified by this generator.
     * @throws Exception -- TODO: Remove or narrow!
     */
    public abstract List<CompilationUnit> generate();

    /**
     * @param node The node to which the {@code @Annotated} annotation will be added.
     * @param qualifiedGeneratorName
     * @param <T>
     */
    public static <T extends Node & NodeWithAnnotations<?>> void annotateGenerated(T node, String qualifiedGeneratorName) {
        AbstractGenerator.annotate(node, Generated.class, new StringLiteralExpr(qualifiedGeneratorName));
//        this.annotateWithTimestamp(node, Generated.class, new StringLiteralExpr(qualifiedGeneratorName));
    }

    /**
     * @param node The node to which the {@code @SuppressWarnings} annotation will be added.
     * @param <T>
     */
    public static <T extends Node & NodeWithAnnotations<?>> void annotateSuppressWarnings(T node) {
        AbstractGenerator.annotate(node, SuppressWarnings.class, new StringLiteralExpr("unchecked"));
    }

    /**
     * @param method The node to which the {@code @Override} annotation will be added.
     */
    public static void annotateOverridden(MethodDeclaration method) {
        AbstractGenerator.annotate(method, Override.class, null);
    }

    /**
     * @param node       The node to which the annotation will be added.
     * @param annotation The annotation to be added to the given node.
     * @param content    Where an annotation has content, it is passed here (otherwise null).
     * @param <T>
     */
    public static <T extends Node & NodeWithAnnotations<?>> void annotate(T node, Class<?> annotation, Expression content) {
        node.setAnnotations(
                node.getAnnotations()
                        .stream()
                        .filter(a -> !a.getNameAsString().equals(annotation.getSimpleName()))
                        .collect(toNodeList())
        );

        if (content != null) {
            node.addSingleMemberAnnotation(annotation.getSimpleName(), content);
        } else {
            node.addMarkerAnnotation(annotation.getSimpleName());
        }

        // The annotation class will normally need to be imported.
        node.tryAddImportToParentCompilationUnit(annotation);
    }

    /**
     * @param node       The node to which the annotation will be added.
     * @param annotation The annotation to be added to the given node.
     * @param content    Where an annotation has content, it is passed here (otherwise null).
     * @param <T>
     */
    private <T extends Node & NodeWithAnnotations<?>> void annotateWithTimestamp(T node, Class<?> annotation, Expression content) {
        node.setAnnotations(
                node.getAnnotations()
                        .stream()
                        .filter(a -> !a.getNameAsString().equals(annotation.getSimpleName()))
                        .collect(toNodeList())
        );

        NormalAnnotationExpr newAnnotation = new NormalAnnotationExpr();
        newAnnotation.setName(annotation.getSimpleName());
        if (content != null) {
            newAnnotation.addPair("qualifiedGeneratorName", content);
        }

        newAnnotation.addPair("timestamp", CoreGenerator.GENERATOR_INIT_TIMESTAMP);
        node.addAnnotation(newAnnotation);

        // The annotation class will normally need to be imported.
        node.tryAddImportToParentCompilationUnit(annotation);
    }

    /**
     * Utility method that looks for a method or constructor with an identical signature as "callable" and replaces it
     * with callable. If not found, adds callable. When the new callable has no javadoc, any old javadoc will be kept.
     */
    protected void addOrReplaceWhenSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        this.addOrReplaceMethod(containingClassOrInterface, callable, () -> {
            AbstractGenerator.annotateGenerated(callable, this.getClass().getName());
            containingClassOrInterface.addMember(callable);
        });
    }

    /**
     * Utility method that looks for a method or constructor with an identical signature as "callable" and replaces it
     * with callable. If not found, fails. When the new callable has no javadoc, any old javadoc will be kept. The
     * method or constructor is annotated with the generator class.
     */
    protected void replaceWhenSameSignature(ClassOrInterfaceDeclaration containingClassOrInterface, CallableDeclaration<?> callable) {
        this.addOrReplaceMethod(containingClassOrInterface, callable,
                () -> {
                    throw new AssertionError(f("Wanted to regenerate a method with signature %s in %s, but it wasn't there.", callable.getSignature(), containingClassOrInterface.getNameAsString()));
                });
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
            callable.setJavadocComment(callable.getJavadocComment().orElse(existingCallable.getJavadocComment().orElse(null)));

            // Mark the method as having been fully/partially generated.
            AbstractGenerator.annotateGenerated(callable, this.getClass().getName());

            // Do the replacement.
            containingClassOrInterface.getMembers().replace(existingCallable, callable);
        }
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

    protected List<CompilationUnit> getParsedCompilationUnitsFromSourceRoot(SourceRoot sourceRoot) throws IOException {
        List<CompilationUnit> cus = sourceRoot.getCompilationUnits();
        List<ParseResult<CompilationUnit>> parseResults = sourceRoot.tryToParse();

        boolean allParsed = parseResults.stream().allMatch(ParseResult::isSuccessful);
        if (!allParsed) {
            List<ParseResult<CompilationUnit>> problemResults = parseResults.stream().filter(compilationUnitParseResult -> !compilationUnitParseResult.isSuccessful()).collect(Collectors.toList());
            for (int i = 0; i < problemResults.size(); i++) {
                ParseResult<CompilationUnit> parseResult = problemResults.get(i);
                List<Problem> problems = parseResult.getProblems();
                System.out.println();
                System.out.println("Problems (" + (i + 1) + " of " + problemResults.size() + "): ");
                System.out.println(problems);
            }

            throw new IllegalStateException("Expected all files to parse.");
        }

        System.out.println("parseResults.size() = " + parseResults.size());

        return parseResults.stream()
                .map(ParseResult::getResult)
                .map(Optional::get)
                .collect(Collectors.toList());
    }

    @Override
    public String toString() {
        return "AbstractGenerator{" +
                "sourceRoot=" + this.sourceRoot +
                ", editedCus=" + this.editedCus +
                '}';
    }
}
