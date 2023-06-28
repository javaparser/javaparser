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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithExtends;
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.ConstructorResolutionLogic;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;

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

    /**
     * @deprecated Consider using {@link #solveType(String, List)} to consider type arguments.
     */
    @Deprecated
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        return solveType(name, null);
    }

    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> typeArguments) {
        if (this.wrappedNode.getName().getId().equals(name)) {
            return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(wrappedNode));
        }

        // Internal classes
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member.isTypeDeclaration()) {
                TypeDeclaration<?> internalType = member.asTypeDeclaration();
                if (internalType.getName().getId().equals(name) && compareTypeParameters(internalType, typeArguments)) {
                    return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(internalType));
                }
                            if (name.startsWith(wrappedNode.getName().getId() + "." + internalType.getName().getId())) {
                    return JavaParserFactory.getContext(internalType, typeSolver).solveType(name.substring(wrappedNode.getName().getId().length() + 1), typeArguments);
                }
                if (name.startsWith(internalType.getName().getId() + ".")) {
                    return JavaParserFactory.getContext(internalType, typeSolver).solveType(name.substring(internalType.getName().getId().length() + 1), typeArguments);
                }
            }
        }

        // Check if is a type parameter
        if (wrappedNode instanceof NodeWithTypeParameters) {
            NodeWithTypeParameters<?> nodeWithTypeParameters = (NodeWithTypeParameters<?>) wrappedNode;
            for (TypeParameter astTpRaw : nodeWithTypeParameters.getTypeParameters()) {
                if (astTpRaw.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(astTpRaw, typeSolver));
                }
            }
        }

        // Check if the node implements other types
        if (wrappedNode instanceof NodeWithImplements) {
            NodeWithImplements<?> nodeWithImplements = (NodeWithImplements<?>) wrappedNode;
            for (ClassOrInterfaceType implementedType : nodeWithImplements.getImplementedTypes()) {
                if (implementedType.getName().getId().equals(name)) {
                    return context.getParent()
                        .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                        .solveType(implementedType.getNameWithScope(), typeArguments);
                }
            }
        }

        // Check if the node extends other types
        if (wrappedNode instanceof NodeWithExtends) {
            NodeWithExtends<?> nodeWithExtends = (NodeWithExtends<?>) wrappedNode;
            for (ClassOrInterfaceType extendedType : nodeWithExtends.getExtendedTypes()) {
                if (extendedType.getName().getId().equals(name) && compareTypeArguments(extendedType, typeArguments)) {
                    return context.getParent()
                            .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                            .solveType(extendedType.getNameWithScope(), typeArguments);
                }
            }
        }

		// Looking at extended classes and implemented interfaces
		String typeName = isCompositeName(name) ? innerMostPartOfName(name) : name;
		ResolvedTypeDeclaration type = checkAncestorsForType(typeName, this.typeDeclaration);
		// Before accepting this value we need to ensure that
		// - the name is not a composite name (this is probably a local class which is discovered
		//   by the check of ancestors
		// - or the outer most part of the name is equals to the type declaration name.
		//   it could be the case when the name is prefixed by the outer class name (eg outerclass.innerClass)
		// - or the qualified name of the type is the same as the name (in case when the name is
		//   a fully qualified class name like java.util.Iterator
		if (type != null
				&& (!isCompositeName(name)
						|| outerMostPartOfName(name).equals(this.typeDeclaration.getName())
						|| type.getQualifiedName().equals(name))) {
			return SymbolReference.solved(type);
		}

        // Else check parents
        return context.getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveType(name, typeArguments);
    }

    private boolean isCompositeName(String name) {
    	return name.indexOf('.') > -1;
    }

    private String innerMostPartOfName(String name) {
    	return isCompositeName(name) ? name.substring(name.lastIndexOf(".")+1) : name;
    }

    private String outerMostPartOfName(String name) {
    	return isCompositeName(name) ? name.substring(0, name.lastIndexOf(".")) : name;
    }

    private <T extends NodeWithTypeArguments<?>> boolean compareTypes(List<? extends Type> types,
                                                                      List<ResolvedType> resolvedTypeArguments) {
        // If the user want's to solve the type without having prior knowledge of the type arguments.
        if (resolvedTypeArguments == null) {
            return true;
        }

        return types.size() == resolvedTypeArguments.size();
    }

    private <T extends NodeWithTypeArguments<?>> boolean compareTypeArguments(T type, List<ResolvedType> resolvedTypeArguments) {
        return compareTypes(type.getTypeArguments().orElse(new NodeList<>()), resolvedTypeArguments);
    }

    private <T extends NodeWithTypeParameters<?>> boolean compareTypeParameters(T type,
                                                                               List<ResolvedType> resolvedTypeArguments) {
        return compareTypes(type.getTypeParameters(), resolvedTypeArguments);
    }

    private boolean compareTypeParameters(TypeDeclaration<?> typeDeclaration, List<ResolvedType> resolvedTypeArguments) {
        if (typeDeclaration instanceof NodeWithTypeParameters) {
            return compareTypeParameters((NodeWithTypeParameters<?>) typeDeclaration, resolvedTypeArguments);
        }
        return true;
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
                        }
                        return null;
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
            SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic.solveMethodInType(typeSolver.getSolvedJavaLangObject(), name, argumentsTypes, false);
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
        return SymbolReference.unsolved();
    }
}
