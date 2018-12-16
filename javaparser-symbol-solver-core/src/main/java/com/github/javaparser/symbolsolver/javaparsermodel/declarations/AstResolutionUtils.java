/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithConstructors;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
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

    static String getPackageName(Node container) {
        if (container instanceof CompilationUnit) {
            Optional<PackageDeclaration> p = ((CompilationUnit) container).getPackageDeclaration();
            if (p.isPresent()) {
                return p.get().getName().toString();
            }
        } else if (container != null) {
            return getPackageName(container.getParentNode().orElse(null));
        }
        return "";
    }

    static String getClassName(String base, Node container) {
        if (container instanceof com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) {
            String b = getClassName(base, container.getParentNode().orElse(null));
            String cn = ((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) container).getName().getId();
            if (b.isEmpty()) {
                return cn;
            } else {
                return b + "." + cn;
            }
        } else if (container instanceof com.github.javaparser.ast.body.EnumDeclaration) {
            String b = getClassName(base, container.getParentNode().orElse(null));
            String cn = ((com.github.javaparser.ast.body.EnumDeclaration) container).getName().getId();
            if (b.isEmpty()) {
                return cn;
            } else {
                return b + "." + cn;
            }
        } else if (container != null) {
            return getClassName(base, container.getParentNode().orElse(null));
        }
        return base;
    }

    static boolean hasDirectlyAnnotation(NodeWithAnnotations<?> nodeWithAnnotations, TypeSolver typeSolver,
                                         String canonicalName) {
        for (AnnotationExpr annotationExpr : nodeWithAnnotations.getAnnotations()) {
            SymbolReference<ResolvedTypeDeclaration> ref = JavaParserFactory.getContext(annotationExpr, typeSolver)
                    .solveType(annotationExpr.getName().getId());
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

    static <N extends ResolvedReferenceTypeDeclaration> List<ResolvedConstructorDeclaration> getConstructors(NodeWithConstructors<?> wrappedNode,
                                                                TypeSolver typeSolver,
                                                                N container) {
        List<ResolvedConstructorDeclaration> declared = wrappedNode.getConstructors().stream()
                .map(c -> new JavaParserConstructorDeclaration<N>(container, c, typeSolver))
                .collect(Collectors.toList());
        if (declared.isEmpty()) {
            // If there are no constructors insert the default constructor
            return ImmutableList.of(new DefaultConstructorDeclaration<N>(container));
        } else {
            return declared;
        }
    }
}
