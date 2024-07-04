/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.MethodResolutionCapability;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.core.resolution.SymbolResolutionCapability;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Heavily based on JavaParserClassDeclaration
 * @author Federico Tomassetti
 */
// TODO: Check all of this
// TODO: This is mostly a copy of JavaParserClassDeclaration. Refactor to reduce code duplication.
public class JavaParserRecordDeclaration extends AbstractTypeDeclaration
        implements ResolvedRecordDeclaration,
                MethodResolutionCapability,
                MethodUsageResolutionCapability,
                SymbolResolutionCapability {

    ///
    /// Fields
    ///

    private TypeSolver typeSolver;
    private RecordDeclaration wrappedNode;
    private JavaParserTypeAdapter<RecordDeclaration> javaParserTypeAdapter;

    ///
    /// Constructors
    ///

    public JavaParserRecordDeclaration(RecordDeclaration wrappedNode, TypeSolver typeSolver) {
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

        JavaParserRecordDeclaration that = (JavaParserRecordDeclaration) o;

        return wrappedNode.equals(that.wrappedNode);
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    @Override
    public String toString() {
        return "JavaParserClassDeclaration{" + "wrappedNode=" + wrappedNode + '}';
    }

    ///
    /// Public methods: fields
    ///

    /**
     * This method returns both the ResolvedFieldDeclarations for the explicit static fields declared in the
     * record and non-static private fields corresponding to the record parameters. This is done to make
     * the fields of a record consistent across the various models (since the record parameters are considered
     * fields by the Java compiler and runtime).
     */
    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        List<ResolvedFieldDeclaration> fields = javaParserTypeAdapter.getFieldsForDeclaredVariables();

        getAncestors(true).stream()
                .filter(ancestor -> ancestor.getTypeDeclaration().isPresent())
                .forEach(ancestor -> ancestor.getTypeDeclaration()
                        .get()
                        .getAllFields()
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

        wrappedNode
                .getParameters()
                .forEach(parameter -> fields.add(new ResolvedFieldDeclaration() {
                    @Override
                    public boolean isStatic() {
                        return false;
                    }

                    @Override
                    public boolean isVolatile() {
                        return false;
                    }

                    @Override
                    public ResolvedTypeDeclaration declaringType() {
                        return wrappedNode.resolve();
                    }

                    @Override
                    public AccessSpecifier accessSpecifier() {
                        return AccessSpecifier.PRIVATE;
                    }

                    @Override
                    public ResolvedType getType() {
                        return parameter.getType().resolve();
                    }

                    @Override
                    public String getName() {
                        return parameter.getNameAsString();
                    }
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
    public Optional<MethodUsage> solveMethodAsUsage(
            String name,
            List<ResolvedType> argumentTypes,
            Context invocationContext,
            List<ResolvedType> typeParameters) {
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

    public Optional<ResolvedReferenceType> getSuperClass() {
        ResolvedReferenceTypeDeclaration solvedJavaLangRecord = typeSolver.getSolvedJavaLangRecord();
        return Optional.of(new ReferenceTypeImpl(solvedJavaLangRecord));
    }

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
    public List<ResolvedReferenceType> getAllSuperClasses() {
        List<ResolvedReferenceType> superClasses = new ArrayList<>();
        getSuperClass().ifPresent(superClass -> superClasses.add(superClass));
        return superClasses;
    }

    @Override
    public List<ResolvedReferenceType> getAllInterfaces() {
        return null;
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        List<ResolvedConstructorDeclaration> constructors =
                AstResolutionUtils.getConstructors(this.wrappedNode, typeSolver, this).stream()
                        .filter(constructor -> !(constructor instanceof DefaultConstructorDeclaration))
                        .collect(Collectors.toList());

        if (constructors.isEmpty() || !containsCanonicalConstructor(constructors)) {
            constructors.add(new CanonicalRecordConstructor(wrappedNode, typeSolver));
        }

        return constructors;
    }

    private boolean containsCanonicalConstructor(List<ResolvedConstructorDeclaration> constructors) {
        return constructors.stream().anyMatch(constructor -> {
            if (constructor.getNumberOfParams() != wrappedNode.getParameters().size()) {
                return false;
            }
            for (int i = 0; i < constructor.getNumberOfParams(); i++) {
                if (!constructor
                        .getParam(i)
                        .getType()
                        .equals(wrappedNode.getParameter(i).getType().resolve())) {
                    return false;
                }
            }
            return true;
        });
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
        String otherName = other.getQualifiedName();
        // Records cannot be extended
        if (otherName.equals(this.getQualifiedName())) {
            return true;
        }
        if (JAVA_LANG_RECORD.equals(otherName)) {
            return true;
        }
        // Enum implements Comparable and Serializable
        if (otherName.equals(JAVA_LANG_COMPARABLE)) {
            return true;
        }
        if (otherName.equals(JAVA_IO_SERIALIZABLE)) {
            return true;
        }

        // TODO FIXME: Remove null check -- should be an empty list...
        if (this.wrappedNode.getImplementedTypes() != null) {
            for (ClassOrInterfaceType type : wrappedNode.getImplementedTypes()) {
                ResolvedReferenceTypeDeclaration ancestor =
                        (ResolvedReferenceTypeDeclaration) new SymbolSolver(typeSolver).solveType(type);
                if (ancestor.canBeAssignedTo(other)) {
                    return true;
                }
            }
        }

        return other.isJavaLangObject();
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
            return new JavaParserRecordDeclaration(this.wrappedNode, typeSolver)
                    .solveType(name.substring(prefix.length()));
        }

        return getContext()
                .getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveType(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {

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
        Optional<ResolvedReferenceTypeDeclaration> resolvedReferenceTypeDeclaration =
                candidateAncestor.getTypeDeclaration();
        if (resolvedReferenceTypeDeclaration.isPresent()) {
            ResolvedTypeDeclaration rtd = resolvedReferenceTypeDeclaration.get().asType();
            // do not consider an inner or nested class as an ancestor
            return !rtd.hasInternalType(ownQualifiedName);
        }
        return false;
    }

    /**
     * This method returns both the explicit methods declared in the record and the implicit getter
     * methods for the record parameters. This is done for consistency across the various models.
     */
    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        Set<ResolvedMethodDeclaration> methods = new HashSet<>();
        for (BodyDeclaration<?> member : wrappedNode.getMembers()) {
            if (member instanceof MethodDeclaration) {
                methods.add(new JavaParserMethodDeclaration((MethodDeclaration) member, typeSolver));
            }
        }
        for (Parameter parameter : wrappedNode.getParameters()) {
            methods.add(new ImplicitGetterMethod(parameter, wrappedNode, typeSolver));
        }
        return methods;
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return this.wrappedNode.getTypeParameters().stream()
                .map((tp) -> new JavaParserTypeParameter(tp, typeSolver))
                .collect(Collectors.toList());
    }

    /**
     * Returns the JavaParser node associated with this JavaParserClassDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public RecordDeclaration getWrappedNode() {
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

        // Since this is used to resolve reference to "extended" and "implemented" types, and since these type
        // references
        // should not be resolved against member types of the current type, we resolve based on the context containing
        // the class declaration.
        // TODO: solveType with type arguments
        SymbolReference<ResolvedTypeDeclaration> ref = getContext()
                .getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveType(className);

        // If unable to solve by the class name alone, attempt to qualify it.
        // TODO: solveType with type arguments
        if (!ref.isSolved()) {
            Optional<ClassOrInterfaceType> localScope = classOrInterfaceType.getScope();
            if (localScope.isPresent()) {
                String localName = localScope.get().getName().getId() + "."
                        + classOrInterfaceType.getName().getId();
                ref = getContext()
                        .getParent()
                        .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                        .solveType(localName);
            }
        }

        // If still unable to resolve, throw an exception.
        if (!ref.isSolved()) {
            throw new UnsolvedSymbolException(classOrInterfaceType.getName().getId());
        }

        if (!classOrInterfaceType.getTypeArguments().isPresent()) {
            return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType());
        }

        List<ResolvedType> superClassTypeParameters = classOrInterfaceType.getTypeArguments().get().stream()
                .map(ta -> new LazyType(v -> JavaParserFacade.get(typeSolver).convert(ta, ta)))
                .collect(Collectors.toList());

        return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType(), superClassTypeParameters);
    }

    public static class ImplicitGetterMethod implements ResolvedMethodDeclaration, TypeVariableResolutionCapability {

        private Parameter correspondingParameter;
        private RecordDeclaration recordDeclaration;
        private TypeSolver typeSolver;

        public ImplicitGetterMethod(
                Parameter correspondingParameter, RecordDeclaration recordDeclaration, TypeSolver typeSolver) {
            this.correspondingParameter = correspondingParameter;
            this.recordDeclaration = recordDeclaration;
            this.typeSolver = typeSolver;
        }

        @Override
        public AccessSpecifier accessSpecifier() {
            return AccessSpecifier.PUBLIC;
        }

        @Override
        public String getName() {
            return correspondingParameter.getNameAsString();
        }

        @Override
        public ResolvedType getReturnType() {
            return correspondingParameter.getType().resolve();
        }

        @Override
        public boolean isAbstract() {
            return false;
        }

        @Override
        public boolean isDefaultMethod() {
            return false;
        }

        @Override
        public boolean isStatic() {
            return false;
        }

        @Override
        public String toDescriptor() {
            return String.format("()%s", getReturnType().toDescriptor());
        }

        @Override
        public ResolvedReferenceTypeDeclaration declaringType() {
            return recordDeclaration.resolve();
        }

        @Override
        public int getNumberOfParams() {
            return 0;
        }

        @Override
        public ResolvedParameterDeclaration getParam(int i) {
            throw new UnsupportedOperationException("Implicit record getter methods do not have parameters");
        }

        @Override
        public int getNumberOfSpecifiedExceptions() {
            return 0;
        }

        @Override
        public ResolvedType getSpecifiedException(int index) {
            throw new UnsupportedOperationException("Implicit record getter methods do not throw exceptions");
        }

        @Override
        public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
            return Collections.emptyList();
        }

        @Override
        public MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes) {
            return new MethodUsage(this);
        }

        @Override
        public Optional<Node> toAst() {
            return Optional.of(recordDeclaration);
        }
    }

    public static class CanonicalRecordConstructor implements ResolvedConstructorDeclaration {

        private RecordDeclaration recordDeclaration;
        private TypeSolver typeSolver;

        public CanonicalRecordConstructor(RecordDeclaration recordDeclaration, TypeSolver typeSolver) {
            this.recordDeclaration = recordDeclaration;
            this.typeSolver = typeSolver;
        }

        @Override
        public AccessSpecifier accessSpecifier() {
            return AccessSpecifier.PUBLIC;
        }

        @Override
        public ResolvedReferenceTypeDeclaration declaringType() {
            return recordDeclaration.resolve();
        }

        @Override
        public int getNumberOfParams() {
            return recordDeclaration.getParameters().size();
        }

        @Override
        public ResolvedParameterDeclaration getParam(int i) {
            // TODO: Should this be a copy?
            return recordDeclaration.getParameters().get(i).resolve();
        }

        @Override
        public int getNumberOfSpecifiedExceptions() {
            return 0;
        }

        @Override
        public ResolvedType getSpecifiedException(int index) {
            throw new UnsupportedOperationException("The canonical record constructor does not throw any exceptions");
        }

        @Override
        public String getName() {
            return recordDeclaration.getNameAsString();
        }

        @Override
        public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
            return Collections.emptyList();
        }
    }
}
