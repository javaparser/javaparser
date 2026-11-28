/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithMembers;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeAdapter<
        T extends Node & NodeWithSimpleName<T> & NodeWithMembers<T> & NodeWithAnnotations<T>> {

    private T wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserTypeAdapter(T wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    public String getPackageName() {
        return AstResolutionUtils.getPackageName(wrappedNode);
    }

    public String getClassName() {
        return AstResolutionUtils.getClassName("", wrappedNode);
    }

    public String getQualifiedName() {
        String containerName =
                AstResolutionUtils.containerName(wrappedNode.getParentNode().orElse(null));
        if (containerName.isEmpty()) {
            return wrappedNode.getName().getId();
        }
        return containerName + "." + wrappedNode.getName().getId();
    }

    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        List<ResolvedReferenceType> ancestorsOfOther = other.getAllAncestors();
        ancestorsOfOther.add(new ReferenceTypeImpl(other));
        for (ResolvedReferenceType ancestorOfOther : ancestorsOfOther) {
            if (ancestorOfOther.getQualifiedName().equals(this.getQualifiedName())) {
                return true;
            }
        }
        return false;
    }

    public boolean isAssignableBy(ResolvedType type) {
        if (type.isNull()) {
            return true;
        }
        if (type.isReferenceType()) {
            ResolvedReferenceTypeDeclaration other = typeSolver.solveType(type.describe());
            return isAssignableBy(other);
        }
        throw new UnsupportedOperationException();
    }

    /**
     * Resolution should move out of declarations, so that they are pure declarations and the resolution should
     * work for JavaParser, Reflection and Javassist classes in the same way and not be specific to the three
     * implementations.
     */
    @Deprecated
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        if (wrappedNode instanceof NodeWithTypeParameters<?>) {
            NodeList<TypeParameter> typeParameters = ((NodeWithTypeParameters<?>) wrappedNode).getTypeParameters();
            for (com.github.javaparser.ast.type.TypeParameter typeParameter : typeParameters) {
                if (typeParameter.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeVariableDeclaration(typeParameter, typeSolver));
                }
            }
        }

        // Member classes & interfaces
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                com.github.javaparser.ast.body.TypeDeclaration<?> internalType =
                        (com.github.javaparser.ast.body.TypeDeclaration<?>) member;
                String prefix = internalType.getName().asString() + ".";
                if (internalType.getName().getId().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        if (((ClassOrInterfaceDeclaration) internalType).isInterface()) {
                            return SymbolReference.solved(new JavaParserInterfaceDeclaration(
                                    (com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType,
                                    typeSolver));
                        }
                        return SymbolReference.solved(new JavaParserClassDeclaration(
                                (com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                    }
                    if (internalType instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration(
                                (com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver));
                    }
                    if (internalType instanceof AnnotationDeclaration) {
                        return SymbolReference.solved(new JavaParserAnnotationDeclaration(
                                (com.github.javaparser.ast.body.AnnotationDeclaration) internalType, typeSolver));
                    }
                    if (internalType instanceof RecordDeclaration) {
                        return SymbolReference.solved(new JavaParserRecordDeclaration(
                                (com.github.javaparser.ast.body.RecordDeclaration) internalType, typeSolver));
                    }
                    throw new UnsupportedOperationException();
                }
                if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    // The rest of the name denotes a member type of the member type, whatever its kind (JLS 6.5.5.2,
                    // issue #5272), declared or inherited (JLS 8.5, JLS 9.5, issue #5273): resolve it in the context
                    // of the member type
                    return JavaParserFactory.getContext(internalType, typeSolver)
                            .solveType(name.substring(prefix.length()));
                }
            }
        }
        return SymbolReference.unsolved();
    }

    /**
     * Resolves a type name from the body of the wrapped declaration: the declaration itself, its type parameters
     * and member types, a member type qualified by the name of the declaration, then the types in scope in the
     * context containing the declaration.
     *
     * @param declaration the declaration of the wrapped node
     */
    SymbolReference<ResolvedTypeDeclaration> solveType(String name, ResolvedTypeDeclaration declaration) {
        if (wrappedNode.getName().getId().equals(name)) {
            return SymbolReference.solved(declaration);
        }
        SymbolReference<ResolvedTypeDeclaration> ref = solveType(name);
        if (ref.isSolved()) {
            return ref;
        }

        String prefix = wrappedNode.getName().asString() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()) {
            return solveType(name.substring(prefix.length()), declaration);
        }

        return enclosingContext().solveType(name);
    }

    /**
     * Resolves the types of a supertype clause of the wrapped declaration, see
     * {@link #toReferenceType(ClassOrInterfaceType)}.
     *
     * @param acceptIncompleteList whether a type that cannot be resolved is left out instead of failing
     * @throws UnsolvedSymbolException if a type cannot be resolved and an incomplete list is not accepted
     */
    List<ResolvedReferenceType> toReferenceTypes(NodeList<ClassOrInterfaceType> clause, boolean acceptIncompleteList) {
        List<ResolvedReferenceType> types = new ArrayList<>();
        for (ClassOrInterfaceType type : clause) {
            try {
                types.add(toReferenceType(type));
            } catch (UnsolvedSymbolException e) {
                if (!acceptIncompleteList) {
                    throw e;
                }
            }
        }
        return types;
    }

    /**
     * Resolves a type of a supertype clause (extends, implements) of the wrapped declaration.
     *
     * @throws UnsolvedSymbolException if the type cannot be resolved
     */
    ResolvedReferenceType toReferenceType(ClassOrInterfaceType classOrInterfaceType) {
        String typeName = classOrInterfaceType.getName().getId();
        if (classOrInterfaceType.getScope().isPresent()) {
            // The name of the scope, without the comments of the source, which are not part of the name (JLS 3.2,
            // issue #5268)
            typeName = classOrInterfaceType.getScope().get().asString() + "." + typeName;
        }

        // The supertypes are not in the scope of the member types of the declaration (JLS 6.3): resolve them from
        // the context containing the declaration (issue #5254). A qualified name is resolved there too, not by the
        // type solver first: a type in scope is chosen in preference to a package of the same name (JLS 6.4.2), the
        // context falling back on the type solver otherwise (issue #5264).
        // TODO: solveType with type arguments
        SymbolReference<ResolvedTypeDeclaration> ref = enclosingContext().solveType(typeName);

        // A qualified name is never retried with its leading segments dropped: "a.b.C" and "b.C" may
        // denote different types, the declared type itself included (issue #4190).
        if (!ref.isSolved()) {
            throw new UnsolvedSymbolException(classOrInterfaceType.getName().getId());
        }

        if (!classOrInterfaceType.getTypeArguments().isPresent()) {
            return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType());
        }

        List<ResolvedType> typeArguments = classOrInterfaceType.getTypeArguments().get().stream()
                .map(ta -> new LazyType(v -> JavaParserFacade.get(typeSolver).convert(ta, ta)))
                .collect(Collectors.toList());

        return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType(), typeArguments);
    }

    /**
     * The context containing the wrapped declaration, which resolves its supertypes (JLS 6.3) and the type names its
     * body does not declare.
     */
    private Context enclosingContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver)
                .getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."));
    }

    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return wrappedNode
                .getParentNode()
                .filter(parentNode -> !(parentNode instanceof CompilationUnit))
                .map(node -> new JavaSymbolSolver(typeSolver).toTypeDeclaration(node));
    }

    public List<ResolvedFieldDeclaration> getFieldsForDeclaredVariables() {
        List<ResolvedFieldDeclaration> fields = new ArrayList<>();
        if (wrappedNode.getMembers() != null) {
            for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
                if (member.isFieldDeclaration()) {
                    FieldDeclaration field = member.asFieldDeclaration();
                    for (VariableDeclarator vd : field.getVariables()) {
                        fields.add(new JavaParserFieldDeclaration(vd, typeSolver));
                    }
                }
            }
        }
        return fields;
    }

    /*
     * Returns a set of the declared annotation on this type
     */
    public Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations() {
        return wrappedNode.getAnnotations().stream()
                .map(annotation -> new JavaSymbolSolver(typeSolver)
                        .resolveDeclaration(annotation, ResolvedAnnotationDeclaration.class))
                .collect(Collectors.toSet());
    }

    /*
     * Returns a set of the declared methods on this type
     */
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        Set<ResolvedMethodDeclaration> methods = new LinkedHashSet<>();
        for (BodyDeclaration<?> member : wrappedNode.getMembers()) {
            if (member instanceof MethodDeclaration) {
                methods.add(new JavaParserMethodDeclaration((MethodDeclaration) member, typeSolver));
            }
        }
        return methods;
    }

    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        // Use a special Set implementation that avoids calculating the hashCode of the node,
        // since this can be very time-consuming for big node trees, and we are sure there are
        // no duplicates in the members list.
        Set<ResolvedReferenceTypeDeclaration> res = Collections.newSetFromMap(new IdentityHashMap<>());
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof TypeDeclaration) {
                res.add(JavaParserFacade.get(typeSolver).getTypeDeclaration((TypeDeclaration) member));
            }
        }
        return res;
    }
}
