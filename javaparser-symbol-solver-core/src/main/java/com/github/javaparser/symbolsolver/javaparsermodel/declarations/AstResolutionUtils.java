/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithMembers;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.google.common.collect.ImmutableList;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
class AstResolutionUtils {

    static String containerName(Node container) {
        String packageName = getPackageName(container);
        String className = getClassName("", container);
        return packageName +
                ((!packageName.isEmpty() && !className.isEmpty()) ? "." : "") +
                className;
    }

    /*
     * Returns the package name from a node (that can be null) or an empty string
     */
    static String getPackageName(Node container) {
        String packageName = "";
        if (container == null) return packageName;
        Optional<CompilationUnit> cu = container.findCompilationUnit();
        if (cu.isPresent()) {
            packageName = cu.get().getPackageDeclaration().map(pd -> pd.getNameAsString()).orElse("");
        }
        return packageName;
    }

    static String getClassName(String base, Node container) {
        if (container instanceof com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) {
            String b = getClassName(base, container.getParentNode().orElse(null));
            String cn = ((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) container).getName().getId();
            if (b.isEmpty()) {
                return cn;
            }
            return b + "." + cn;
        }
            if (container instanceof com.github.javaparser.ast.body.EnumDeclaration) {
            String b = getClassName(base, container.getParentNode().orElse(null));
            String cn = ((com.github.javaparser.ast.body.EnumDeclaration) container).getName().getId();
            if (b.isEmpty()) {
                return cn;
            }
            return b + "." + cn;
        }
            if (container instanceof com.github.javaparser.ast.body.AnnotationDeclaration) {
            String b = getClassName(base, container.getParentNode().orElse(null));
            String cn = ((com.github.javaparser.ast.body.AnnotationDeclaration) container).getName().getId();
            if (b.isEmpty()) {
                return cn;
            }
            return b + "." + cn;
        }
        if (container != null) {
            return getClassName(base, container.getParentNode().orElse(null));
        }
        return base;
    }

    static boolean hasDirectlyAnnotation(NodeWithAnnotations<?> nodeWithAnnotations, TypeSolver typeSolver,
                                         String canonicalName) {
        for (AnnotationExpr annotationExpr : nodeWithAnnotations.getAnnotations()) {
            SymbolReference<ResolvedTypeDeclaration> ref = JavaParserFactory.getContext(annotationExpr, typeSolver)
                    .solveType(annotationExpr.getNameAsString());
            if (ref.isSolved()) {
                if (ref.getCorrespondingDeclaration().getQualifiedName().equals(canonicalName)) {
                    return true;
                }
            } else {
                throw new UnsolvedSymbolException(annotationExpr.getName().getId());
            }
        }
        return false;
    }

    static <N extends ResolvedReferenceTypeDeclaration> List<ResolvedConstructorDeclaration> getConstructors(
            NodeWithMembers<?> wrappedNode,
            TypeSolver typeSolver,
            N container) {
        List<ResolvedConstructorDeclaration> declared = wrappedNode.getConstructors().stream()
                .map(c -> new JavaParserConstructorDeclaration<N>(container, c, typeSolver))
                .collect(Collectors.toList());
        if (declared.isEmpty()) {
            // If there are no constructors insert the default constructor
            return ImmutableList.of(new DefaultConstructorDeclaration<N>(container));
        }
        return declared;
    }
}
