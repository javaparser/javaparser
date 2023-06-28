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

import java.util.*;
import java.util.stream.Collectors;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.core.resolution.SymbolResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

/**
 * @author Federico Tomassetti
 */
public class JavaParserClassDeclaration extends AbstractClassDeclaration
        implements MethodUsageResolutionCapability, SymbolResolutionCapability {

    ///
    /// Fields
    ///

    private TypeSolver typeSolver;
    private ClassOrInterfaceDeclaration wrappedNode;
    private JavaParserTypeAdapter<ClassOrInterfaceDeclaration> javaParserTypeAdapter;

    ///
    /// Constructors
    ///

    public JavaParserClassDeclaration(ClassOrInterfaceDeclaration wrappedNode,
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

        getAncestors(true).stream().filter(ancestor -> ancestor.getTypeDeclaration().isPresent())
                .forEach(ancestor -> ancestor.getTypeDeclaration().get().getAllFields()
                        .forEach(f -> {
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
                                public boolean isVolatile() {
                                    return f.isVolatile();
                                }

                                @Override
                                public ResolvedTypeDeclaration declaringType() {
                                    return f.declaringType();
                                }

                                @Override
                                public Optional<Node> toAst() {
                                    return f.toAst();
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
    public Optional<ResolvedReferenceType> getSuperClass() {
        if (isJavaLangObject()) {
            // If this is java.lang.Object, it has no super class.
            return Optional.empty();
        }
            if (wrappedNode.getExtendedTypes().isEmpty()) {
            // All objects implicitly extend java.lang.Object -- inject it here (only when this isn't java.lang.Object)
            return Optional.of(object());
        }
        return Optional.of(toReferenceType(wrappedNode.getExtendedTypes().getFirst().get()));
    }

    @Override
    public List<ResolvedReferenceType> getInterfaces() {
        List<ResolvedReferenceType> interfaces = new ArrayList<>();
        // TODO FIXME: Remove null check -- should be an empty list...
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

    /*
     * Returns a set of the declared annotation on this type
     */
    @Override
    public Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations() {
        return javaParserTypeAdapter.getDeclaredAnnotations();
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

        Optional<ResolvedReferenceType> optionalSuperClass = getSuperClass();
        if (optionalSuperClass.isPresent()) {
            Optional<ResolvedReferenceTypeDeclaration> optionalSuperclassTypeDeclaration = optionalSuperClass.get().getTypeDeclaration();
            if (optionalSuperclassTypeDeclaration.isPresent()) {
                ResolvedReferenceTypeDeclaration superclassTypeDeclaration = optionalSuperclassTypeDeclaration.get();
                if (superclassTypeDeclaration != this && superclassTypeDeclaration.isClass()) {
                    if (superclassTypeDeclaration.asClass().canBeAssignedTo(other)) {
                        return true;
                    }
                }
            }
        }

        // TODO FIXME: Remove null check -- should be an empty list...
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

        String prefix = wrappedNode.getName().asString() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()) {
            return new JavaParserClassDeclaration(this.wrappedNode, typeSolver).solveType(name.substring(prefix.length()));
        }

        return getContext().getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveType(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes,
                                                                  boolean staticOnly) {
        return getContext().solveMethod(name, argumentsTypes, staticOnly);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return getContext().solveSymbol(name);
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();

        // We want to avoid infinite recursion in case of Object having Object as ancestor
        if (this.isJavaLangObject()) {
            return ancestors;
        }

        Optional<String> qualifiedName = wrappedNode.getFullyQualifiedName();
        if (!qualifiedName.isPresent()) {
            return ancestors;
        }

        try {
            // If a superclass is found, add it as an ancestor
            Optional<ResolvedReferenceType> superClass = getSuperClass();
            if (superClass.isPresent()) {
                if (isAncestor(superClass.get(), qualifiedName.get())) {
                    ancestors.add(superClass.get());
                }
            }
        } catch (UnsolvedSymbolException e) {
            // in case we could not resolve the super class, we may still be able to resolve (some of) the
            // implemented interfaces and so we continue gracefully with an (incomplete) list of ancestors

            if (!acceptIncompleteList) {
                // Only throw if an incomplete ancestor list is unacceptable.
                throw e;
            }
        }

        for (ClassOrInterfaceType implemented : wrappedNode.getImplementedTypes()) {
            try {
                // If an implemented interface is found, add it as an ancestor
                ResolvedReferenceType rrt = toReferenceType(implemented);
                if (isAncestor(rrt, qualifiedName.get())) {
                    ancestors.add(rrt);
                }
            } catch (UnsolvedSymbolException e) {
                // in case we could not resolve some implemented interface, we may still be able to resolve the
                // extended class or (some of) the other implemented interfaces and so we continue gracefully
                // with an (incomplete) list of ancestors

                if (!acceptIncompleteList) {
                    // Only throw if an incomplete ancestor list is unacceptable.
                    throw e;
                }
            }
        }

        return ancestors;
    }

    private boolean isAncestor(ResolvedReferenceType candidateAncestor, String ownQualifiedName) {
        Optional<ResolvedReferenceTypeDeclaration> resolvedReferenceTypeDeclaration = candidateAncestor.getTypeDeclaration();
        if (resolvedReferenceTypeDeclaration.isPresent()) {
            ResolvedTypeDeclaration rtd = resolvedReferenceTypeDeclaration.get().asType();
            // do not consider an inner or nested class as an ancestor
            return !rtd.hasInternalType(ownQualifiedName);
        }
        return false;
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        Set<ResolvedMethodDeclaration> methods = new HashSet<>();
        for (BodyDeclaration<?> member : wrappedNode.getMembers()) {
            if (member instanceof MethodDeclaration) {
                methods.add(new JavaParserMethodDeclaration((MethodDeclaration) member, typeSolver));
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
    public ClassOrInterfaceDeclaration getWrappedNode() {
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
        ResolvedReferenceTypeDeclaration solvedJavaLangObject = typeSolver.getSolvedJavaLangObject();
        return new ReferenceTypeImpl(solvedJavaLangObject);
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        return javaParserTypeAdapter.internalTypes();
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
            return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType());
        }

        List<ResolvedType> superClassTypeParameters = classOrInterfaceType.getTypeArguments().get()
                .stream()
                .map(ta -> new LazyType(v -> JavaParserFacade.get(typeSolver).convert(ta, ta)))
                .collect(Collectors.toList());

        return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType(), superClassTypeParameters);
    }
}
