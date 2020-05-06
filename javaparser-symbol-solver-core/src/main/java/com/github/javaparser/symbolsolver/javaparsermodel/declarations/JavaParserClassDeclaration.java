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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.LazyType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserClassDeclaration extends AbstractClassDeclaration implements MethodUsageResolutionCapability {

    ///
    /// Fields
    ///

    private TypeSolver typeSolver;
    private com.github.javaparser.ast.body.ClassOrInterfaceDeclaration wrappedNode;
    private JavaParserTypeAdapter<ClassOrInterfaceDeclaration> javaParserTypeAdapter;

    ///
    /// Constructors
    ///

    public JavaParserClassDeclaration(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration wrappedNode,
                                      TypeSolver typeSolver) {
        if (wrappedNode.isInterface()) {
            throw new IllegalArgumentException("Interface given");
        }
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
        this.javaParserTypeAdapter = new JavaParserTypeAdapter<>(wrappedNode, typeSolver);
    }

    ///
    /// Public methods: from Object
    ///

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserClassDeclaration that = (JavaParserClassDeclaration) o;

        return wrappedNode.equals(that.wrappedNode);
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    @Override
    public String toString() {
        return "JavaParserClassDeclaration{" +
                "wrappedNode=" + wrappedNode +
                '}';
    }

    ///
    /// Public methods: fields
    ///

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        List<ResolvedFieldDeclaration> fields = javaParserTypeAdapter.getFieldsForDeclaredVariables();

        getAncestors(true).forEach(ancestor -> ancestor.getTypeDeclaration().getAllFields().forEach(f -> {
            fields.add(new ResolvedFieldDeclaration() {

                @Override
                public AccessSpecifier accessSpecifier() {
                    return f.accessSpecifier();
                }

                @Override
                public String getName() {
                    return f.getName();
                }

                @Override
                public ResolvedType getType() {
                    return ancestor.useThisTypeParametersOnTheGivenType(f.getType());
                }

                @Override
                public boolean isStatic() {
                    return f.isStatic();
                }

                @Override
                public ResolvedTypeDeclaration declaringType() {
                    return f.declaringType();
                }
            });
        }));

        return fields;
    }

    ///
    /// Public methods
    ///

    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> parameterTypes) {
        Context ctx = getContext();
        return ctx.solveMethod(name, parameterTypes, false);
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentTypes,
                                                    Context invocationContext, List<ResolvedType> typeParameters) {
        return getContext().solveMethodAsUsage(name, argumentTypes);
    }

    /**
     * This method is deprecated because the context is an implementation detail that should not be exposed.
     * Ideally this method should become private. For this reason all further usages of this method are discouraged.
     */
    @Deprecated
    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    public ResolvedType getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    @Override
    public ResolvedReferenceType getSuperClass() {
        if (wrappedNode.getExtendedTypes().isEmpty()) {
            return object();
        } else {
            return toReferenceType(wrappedNode.getExtendedTypes().get(0));
        }
    }

    @Override
    public List<ResolvedReferenceType> getInterfaces() {
        List<ResolvedReferenceType> interfaces = new ArrayList<>();
        if (wrappedNode.getImplementedTypes() != null) {
            for (ClassOrInterfaceType t : wrappedNode.getImplementedTypes()) {
                interfaces.add(toReferenceType(t));
            }
        }
        return interfaces;
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return AstResolutionUtils.getConstructors(this.wrappedNode, typeSolver, this);
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return AstResolutionUtils.hasDirectlyAnnotation(wrappedNode, typeSolver, canonicalName);
    }

    @Override
    public boolean isInterface() {
        return wrappedNode.isInterface();
    }

    @Override
    public String getPackageName() {
        return javaParserTypeAdapter.getPackageName();
    }

    @Override
    public String getClassName() {
        return javaParserTypeAdapter.getClassName();
    }

    @Override
    public String getQualifiedName() {
        return javaParserTypeAdapter.getQualifiedName();
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return javaParserTypeAdapter.isAssignableBy(other);
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        return javaParserTypeAdapter.isAssignableBy(type);
    }

    @Override
    public boolean canBeAssignedTo(ResolvedReferenceTypeDeclaration other) {
        // TODO consider generic types
        if (this.getQualifiedName().equals(other.getQualifiedName())) {
            return true;
        }
        ResolvedClassDeclaration superclass = (ResolvedClassDeclaration) getSuperClass().getTypeDeclaration();
        if (superclass != null && superclass != this) {
            if (superclass.canBeAssignedTo(other)) {
                return true;
            }
        }

        if (this.wrappedNode.getImplementedTypes() != null) {
            for (ClassOrInterfaceType type : wrappedNode.getImplementedTypes()) {
                ResolvedReferenceTypeDeclaration ancestor = (ResolvedReferenceTypeDeclaration) new SymbolSolver(typeSolver).solveType(type);
                if (ancestor.canBeAssignedTo(other)) {
                    return true;
                }
            }
        }

        return false;
    }

    @Override
    public boolean isTypeParameter() {
        return false;
    }

    /**
     * Resolution should move out of declarations, so that they are pure declarations and the resolution should
     * work for JavaParser, Reflection and Javassist classes in the same way and not be specific to the three
     * implementations.
     */
    @Deprecated
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        if (this.wrappedNode.getName().getId().equals(name)) {
            return SymbolReference.solved(this);
        }
        SymbolReference<ResolvedTypeDeclaration> ref = javaParserTypeAdapter.solveType(name);
        if (ref.isSolved()) {
            return ref;
        }

        String prefix = wrappedNode.getName() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()) {
            return new JavaParserClassDeclaration(this.wrappedNode, typeSolver).solveType(name.substring(prefix.length()));
        }

        return getContext().getParent().solveType(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes,
                                                                  boolean staticOnly) {
        return getContext().solveMethod(name, argumentsTypes, staticOnly);
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();

        // We want to avoid infinite recursion in case of Object having Object as ancestor
        if (!(Object.class.getCanonicalName().equals(getQualifiedName()))) {
            ResolvedReferenceType superclass;
            try {
                superclass = getSuperClass();
            } catch (UnsolvedSymbolException e) {
                if (acceptIncompleteList) {
                    // in case we could not resolve the super class, we may still be able to resolve (some of) the
                    // implemented interfaces and so we continue gracefully with an (incomplete) list of ancestors
                    superclass = null;
                } else {
                    throw e;
                }
            }
            if (superclass != null) {
                ancestors.add(superclass);
            }
            if (wrappedNode.getImplementedTypes() != null) {
                for (ClassOrInterfaceType implemented : wrappedNode.getImplementedTypes()) {
                    ResolvedReferenceType ancestor;
                    try {
                        ancestor = toReferenceType(implemented);
                    } catch (UnsolvedSymbolException e) {
                        if (acceptIncompleteList) {
                            // in case we could not resolve some implemented interface, we may still be able to resolve the
                            // extended class or (some of) the other implemented interfaces and so we continue gracefully
                            // with an (incomplete) list of ancestors
                            ancestor = null;
                        } else {
                            throw e;
                        }
                    }
                    if (ancestor != null) {
                        ancestors.add(ancestor);
                    }
                }
            }
        }

        return ancestors;
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        Set<ResolvedMethodDeclaration> methods = new HashSet<>();
        for (BodyDeclaration<?> member : wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.MethodDeclaration) {
                methods.add(new JavaParserMethodDeclaration((com.github.javaparser.ast.body.MethodDeclaration) member, typeSolver));
            }
        }
        return methods;
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return this.wrappedNode.getTypeParameters().stream().map(
                (tp) -> new JavaParserTypeParameter(tp, typeSolver)
        ).collect(Collectors.toList());
    }

    /**
     * Returns the JavaParser node associated with this JavaParserClassDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public com.github.javaparser.ast.body.ClassOrInterfaceDeclaration getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return wrappedNode.getAccessSpecifier();
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.of(wrappedNode);
    }

    ///
    /// Protected methods
    ///

    @Override
    protected ResolvedReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        Set<ResolvedReferenceTypeDeclaration> res = new HashSet<>();
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                res.add(JavaParserFacade.get(typeSolver).getTypeDeclaration((com.github.javaparser.ast.body.TypeDeclaration) member));
            }
        }
        return res;
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return javaParserTypeAdapter.containerType();
    }

    ///
    /// Private methods
    ///

    private ResolvedReferenceType toReferenceType(ClassOrInterfaceType classOrInterfaceType) {
        String className = classOrInterfaceType.getName().getId();
        if (classOrInterfaceType.getScope().isPresent()) {
            // look for the qualified name (for example class of type Rectangle2D.Double)
            className = classOrInterfaceType.getScope().get().toString() + "." + className;
        }
        SymbolReference<ResolvedTypeDeclaration> ref = solveType(className);

        // If unable to solve by the class name alone, attempt to qualify it.
        if (!ref.isSolved()) {
            Optional<ClassOrInterfaceType> localScope = classOrInterfaceType.getScope();
            if (localScope.isPresent()) {
                String localName = localScope.get().getName().getId() + "." + classOrInterfaceType.getName().getId();
                ref = solveType(localName);
            }
        }

        // If still unable to resolve, throw an exception.
        if (!ref.isSolved()) {
            throw new UnsolvedSymbolException(classOrInterfaceType.getName().getId());
        }

        if (!classOrInterfaceType.getTypeArguments().isPresent()) {
            return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType(), typeSolver);
        }

        List<ResolvedType> superClassTypeParameters = classOrInterfaceType.getTypeArguments().get()
                .stream()
                .map(ta -> new LazyType(v -> JavaParserFacade.get(typeSolver).convert(ta, ta)))
                .collect(Collectors.toList());

        return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType(), superClassTypeParameters, typeSolver);
    }
}
