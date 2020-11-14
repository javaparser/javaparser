/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.declarations.HasAccessSpecifier;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.ConstructorResolutionLogic;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeDeclarationAdapter {

    private com.github.javaparser.ast.body.TypeDeclaration<?> wrappedNode;
    private TypeSolver typeSolver;
    private Context context;
    private ResolvedReferenceTypeDeclaration typeDeclaration;

    public JavaParserTypeDeclarationAdapter(com.github.javaparser.ast.body.TypeDeclaration<?> wrappedNode, TypeSolver typeSolver,
                                            ResolvedReferenceTypeDeclaration typeDeclaration,
                                            Context context) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
        this.typeDeclaration = typeDeclaration;
        this.context = context;
    }

    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        if (this.wrappedNode.getName().getId().equals(name)) {
            return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(wrappedNode));
        }

        // Internal classes
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                com.github.javaparser.ast.body.TypeDeclaration<?> internalType = (com.github.javaparser.ast.body.TypeDeclaration<?>) member;
                if (internalType.getName().getId().equals(name)) {
                    return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(internalType));
                } else if (name.startsWith(String.format("%s.%s", wrappedNode.getName(), internalType.getName()))) {
                    return JavaParserFactory.getContext(internalType, typeSolver).solveType(name.substring(wrappedNode.getName().getId().length() + 1));
                } else if (name.startsWith(String.format("%s.", internalType.getName()))) {
                    return JavaParserFactory.getContext(internalType, typeSolver).solveType(name.substring(internalType.getName().getId().length() + 1));
                }
            }
        }

        if (wrappedNode instanceof NodeWithTypeParameters) {
            NodeWithTypeParameters<?> nodeWithTypeParameters = (NodeWithTypeParameters<?>) wrappedNode;
            for (TypeParameter astTpRaw : nodeWithTypeParameters.getTypeParameters()) {
                TypeParameter astTp = astTpRaw;
                if (astTp.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(astTp, typeSolver));
                }
            }
        }

        // Look into extended classes and implemented interfaces
        ResolvedTypeDeclaration type = checkAncestorsForType(name, this.typeDeclaration);
        if (type != null) {
            return SymbolReference.solved(type);
        }

        // Else check parents
        return context.getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveType(name);
    }

    /**
     * Recursively checks the ancestors of the {@param declaration} if an internal type is declared with a name equal
     * to {@param name}.
     * TODO: Edit to remove return of null (favouring a return of optional)
     * @return A ResolvedTypeDeclaration matching the {@param name}, null otherwise
     */
    private ResolvedTypeDeclaration checkAncestorsForType(String name, ResolvedReferenceTypeDeclaration declaration) {
        for (ResolvedReferenceType ancestor : declaration.getAncestors(true)) {
            try {
                // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
                ResolvedReferenceTypeDeclaration ancestorReferenceTypeDeclaration = ancestor
                        .getTypeDeclaration()
                        .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."));

                for (ResolvedTypeDeclaration internalTypeDeclaration : ancestorReferenceTypeDeclaration.internalTypes()) {
                    boolean visible = true;
                    if (internalTypeDeclaration instanceof ResolvedReferenceTypeDeclaration) {
                        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = internalTypeDeclaration.asReferenceType();
                        if (resolvedReferenceTypeDeclaration instanceof HasAccessSpecifier) {
                            visible = ((HasAccessSpecifier) resolvedReferenceTypeDeclaration).accessSpecifier() != AccessSpecifier.PRIVATE;
                        }
                    }
                    if (internalTypeDeclaration.getName().equals(name)) {
                        if (visible) {
                            return internalTypeDeclaration;
                        } else {
                            return null; // FIXME -- Avoid returning null.
                        }
                    }
                }

                // check recursively the ancestors of this ancestor
                ResolvedTypeDeclaration ancestorTypeDeclaration = checkAncestorsForType(name, ancestorReferenceTypeDeclaration);
                if (ancestorTypeDeclaration != null) {
                    return ancestorTypeDeclaration;
                }
            } catch (UnsupportedOperationException e) {
                // just continue using the next ancestor
            }
        }
        return null; // FIXME -- Avoid returning null.
    }

    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {

        // Begin by locating methods declared "here"
        List<ResolvedMethodDeclaration> candidateMethods = typeDeclaration.getDeclaredMethods().stream()
                .filter(m -> m.getName().equals(name))
                .filter(m -> !staticOnly || m.isStatic())
                .collect(Collectors.toList());

        // Next, consider methods declared within ancestors.
        // Note that we only consider ancestors when we are not currently at java.lang.Object (avoiding infinite recursion).
        if (!typeDeclaration.isJavaLangObject()) {
            for (ResolvedReferenceType ancestor : typeDeclaration.getAncestors(true)) {
                Optional<ResolvedReferenceTypeDeclaration> ancestorTypeDeclaration = ancestor.getTypeDeclaration();

                // Avoid recursion on self
                if (ancestor.getTypeDeclaration().isPresent() && typeDeclaration != ancestorTypeDeclaration.get()) {
                    // Consider methods declared on self
                    candidateMethods.addAll(ancestor.getAllMethodsVisibleToInheritors()
                            .stream()
                            .filter(m -> m.getName().equals(name))
                            .collect(Collectors.toList()));

                    // consider methods from superclasses and only default methods from interfaces :
                    // not true, we should keep abstract as a valid candidate
                    // abstract are removed in MethodResolutionLogic.isApplicable is necessary
                    SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic.solveMethodInType(ancestorTypeDeclaration.get(), name, argumentsTypes, staticOnly);
                    if (res.isSolved()) {
                        candidateMethods.add(res.getCorrespondingDeclaration());
                    }
                }
            }
        }

        // If we haven't located any candidates that are declared on this type or its ancestors, consider the parent context.
        // This is relevant e.g. with nested classes.
        // Note that we want to avoid infinite recursion when a class is using its own method - see issue #75
        if (candidateMethods.isEmpty()) {
            SymbolReference<ResolvedMethodDeclaration> parentSolution = context.getParent()
                    .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                    .solveMethod(name, argumentsTypes, staticOnly);
            if (parentSolution.isSolved()) {
                candidateMethods.add(parentSolution.getCorrespondingDeclaration());
            }
        }

        // if is interface and candidate method list is empty, we should check the Object Methods
        if (candidateMethods.isEmpty() && typeDeclaration.isInterface()) {
            SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic.solveMethodInType(new ReflectionClassDeclaration(Object.class, typeSolver), name, argumentsTypes, false);
            if (res.isSolved()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        }

        return MethodResolutionLogic.findMostApplicable(candidateMethods, name, argumentsTypes, typeSolver);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solveConstructor(List<ResolvedType> argumentsTypes) {
        if (typeDeclaration instanceof ResolvedClassDeclaration) {
            return ConstructorResolutionLogic.findMostApplicable(typeDeclaration.getConstructors(), argumentsTypes, typeSolver);
        }
        return SymbolReference.unsolved(ResolvedConstructorDeclaration.class);
    }
}
