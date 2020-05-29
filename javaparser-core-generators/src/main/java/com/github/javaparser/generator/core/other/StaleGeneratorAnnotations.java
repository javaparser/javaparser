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

package com.github.javaparser.generator.core.other;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.StaleGenerated;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.generator.AbstractGenerator;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class StaleGeneratorAnnotations extends AbstractGenerator {

    public StaleGeneratorAnnotations(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    public void generate() throws Exception {
        Log.info("Running %s", () -> getClass().getSimpleName());

        List<CompilationUnit> parsedCus = getParsedCompilationUnitsFromSourceRoot(sourceRoot);

        Log.info("parsedCus.size() = " + parsedCus.size());
        parsedCus.forEach(compilationUnit -> {
            List<AnnotationExpr> allAnnotations = compilationUnit.findAll(AnnotationExpr.class);
            allAnnotations.stream()
                    .filter(annotationExpr -> annotationExpr.getName().asString().equals(Generated.class.getSimpleName()))
                    .forEach(annotationExpr -> {
                        annotationExpr.getParentNode()
                                .ifPresent(node -> {
                                    NodeWithAnnotations<?> annotatedNode = (NodeWithAnnotations<?>) node;
                                    annotateStale(annotatedNode);
                                });
                    });

//            // Remove the import. -- TODO: Fix this (causes java.util.ConcurrentModificationException)
//            compilationUnit.getImports().removeIf(importDeclaration -> importDeclaration.getName().asString().equals(Generated.class.getCanonicalName()));
//            for (ImportDeclaration importDeclaration : compilationUnit.getImports()) {
//                if (importDeclaration.getName().asString().equals(Generated.class.getCanonicalName())) {
//                    Log.info("importDeclaration.getName().asString() = " + importDeclaration.getName().asString());
//                    Log.info("Generated.class.getCanonicalName()     = " + Generated.class.getCanonicalName());
//                    importDeclaration.remove();
//
//                    // Mark this CU as having been edited.
//                    this.editedCus.add(compilationUnit);
//                }
//            }

        });

        after();
    }

    public void removeStaleImportIfUnused() throws IOException {
        Log.info("Running %s", () -> getClass().getSimpleName());

        List<CompilationUnit> parsedCus = getParsedCompilationUnitsFromSourceRoot(sourceRoot);
        Log.info("parsedCus.size() = " + parsedCus.size());

        parsedCus.forEach(compilationUnit -> {
            // Remove unused @StaleGenerated import
            removeAnnotationImportIfUnused(compilationUnit, StaleGenerated.class);
        });
    }

    public void removeGeneratedImportIfUnused() throws IOException {
        Log.info("Running %s", () -> getClass().getSimpleName());

        List<CompilationUnit> parsedCus = getParsedCompilationUnitsFromSourceRoot(sourceRoot);
        Log.info("parsedCus.size() = " + parsedCus.size());

        parsedCus.forEach(compilationUnit -> {
            // Remove unused @StaleGenerated import
            removeAnnotationImportIfUnused(compilationUnit, Generated.class);
        });
    }

    public void verify() throws IOException {
        Log.info("Running %s", () -> getClass().getSimpleName());

        List<CompilationUnit> parsedCus = getParsedCompilationUnitsFromSourceRoot(sourceRoot);

        Log.info("parsedCus.size() = " + parsedCus.size());

        List<String> errors = new ArrayList<>();

        parsedCus.forEach(compilationUnit -> {
            // Check
            List<AnnotationExpr> allAnnotations = compilationUnit.findAll(AnnotationExpr.class);
            allAnnotations.stream()
                    .filter(annotationExpr -> annotationExpr.getName().asString().equals(StaleGenerated.class.getSimpleName()))
                    .forEach(annotationExpr -> {
                        String lineNumber = "";
                        if (annotationExpr.getRange().isPresent()) {
                            lineNumber = ":" + annotationExpr.getRange().get().begin.line;
//                        } else if (annotationExpr.getParentNode().isPresent() && annotationExpr.getParentNode().get().getRange().isPresent()) {
//                            // Commented out as unreliable due to AST modifications
//                            lineNumber = ":" + annotationExpr.getParentNode().get().getRange().get().begin.line + " (parent node line)";
                        } else {
                            lineNumber = " (no line #)";
                        }

                        errors.add(
                                "Annotation of @StaleGenerated found within: " +
                                        compilationUnit.getStorage().get().getPath().toString() +
                                        lineNumber
                        );
                    });
        });

        if (!errors.isEmpty()) {
            StringBuilder sb = new StringBuilder();
            sb.append("ERROR: (" + errors.size() + ") @StaleGenerated Found: ");
            for (int i = 0; i < errors.size(); i++) {
                String s = errors.get(i);
                sb.append("\n    " + i + ": " + s);
            }

//            throw new RuntimeException(sb.toString());
            System.err.println(sb.toString());
        }
    }
}
