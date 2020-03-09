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

import com.github.javaparser.ParseResult;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.io.IOException;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class RemoveGeneratorAnnotations {

    private SourceRoot sourceRoot;

    public RemoveGeneratorAnnotations(SourceRoot sourceRoot) {
        this.sourceRoot = sourceRoot;
    }

    public void generate() throws IOException {
        Log.info("Running %s", () -> getClass().getSimpleName());

        List<CompilationUnit> parsedCus = getParsedCompilationUnitsFromSourceRoot(sourceRoot);
        parsedCus.forEach(compilationUnit -> {
            removeAnnotations(compilationUnit);
//            removeImports(compilationUnit);
        });
    }

    public void removeImports(CompilationUnit compilationUnit) {
        // Remove the import. -- TODO: Fix this (causes java.util.ConcurrentModificationException)
        compilationUnit.getImports().removeIf(importDeclaration -> importDeclaration.getName().asString().equals(Generated.class.getCanonicalName()));
        for (ImportDeclaration importDeclaration : compilationUnit.getImports()) {
            if (importDeclaration.getName().asString().equals(Generated.class.getCanonicalName())) {
                Log.info("importDeclaration.getName().asString() = " + importDeclaration.getName().asString());
                Log.info("Generated.class.getCanonicalName()     = " + Generated.class.getCanonicalName());
                importDeclaration.remove();
            }
        }
    }

    public void removeAnnotations(CompilationUnit compilationUnit) {
        List<AnnotationExpr> allAnnotations = compilationUnit.findAll(AnnotationExpr.class);
        // Remove the annotation -- TODO: should likely be a replace operation.
        allAnnotations.stream()
                .filter(annotationExpr -> annotationExpr.getName().asString().equals(Generated.class.getSimpleName()))
                .forEach(Node::remove);
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


}
