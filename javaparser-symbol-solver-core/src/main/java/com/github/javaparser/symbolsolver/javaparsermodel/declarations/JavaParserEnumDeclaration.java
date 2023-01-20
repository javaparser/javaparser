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

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
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
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.core.resolution.SymbolResolutionCapability;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;

import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserEnumDeclaration extends AbstractTypeDeclaration
        implements ResolvedEnumDeclaration, MethodResolutionCapability, MethodUsageResolutionCapability,
        SymbolResolutionCapability {

    private static String JAVA_LANG_ENUM = java.lang.Enum.class.getCanonicalName();
    private static String JAVA_LANG_COMPARABLE = java.lang.Comparable.class.getCanonicalName();
    private static String JAVA_IO_SERIALIZABLE = Serializable.class.getCanonicalName();

    private TypeSolver typeSolver;
    private EnumDeclaration wrappedNode;
    private JavaParserTypeAdapter<com.github.javaparser.ast.body.EnumDeclaration> javaParserTypeAdapter;

    public JavaParserEnumDeclaration(com.github.javaparser.ast.body.EnumDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
        this.javaParserTypeAdapter = new JavaParserTypeAdapter<>(wrappedNode, typeSolver);
    }

    @Override
    public String toString() {
        return "JavaParserEnumDeclaration{" +
                "wrappedNode=" + wrappedNode +
                '}';
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

    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isType() {
        return true;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return AstResolutionUtils.hasDirectlyAnnotation(wrappedNode, typeSolver, canonicalName);
    }

    @Override
    public boolean canBeAssignedTo(ResolvedReferenceTypeDeclaration other) {
        String otherName = other.getQualifiedName();
        // Enums cannot be extended
        if (otherName.equals(this.getQualifiedName())) {
            return true;
        }
        if (otherName.equals(JAVA_LANG_ENUM)) {
            return true;
        }
        // Enum implements Comparable and Serializable
        if (otherName.equals(JAVA_LANG_COMPARABLE)) {
            return true;
        }
        if (otherName.equals(JAVA_IO_SERIALIZABLE)) {
            return true;
        }
        if (other.isJavaLangObject()) {
            return true;
        }
        return false;
    }

    @Override
    public boolean isClass() {
        return false;
    }

    @Override
    public boolean isInterface() {
        return false;
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
    public boolean isTypeParameter() {
        return false;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserEnumDeclaration that = (JavaParserEnumDeclaration) o;

        if (!wrappedNode.equals(that.wrappedNode)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentTypes,
                                                    Context invokationContext, List<ResolvedType> typeParameters) {
        return getContext().solveMethodAsUsage(name, argumentTypes);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes,
                                                                  boolean staticOnly) {
        if (name.equals("values") && argumentsTypes.isEmpty()) {
            return SymbolReference.solved(new JavaParserEnumDeclaration.ValuesMethod(this, typeSolver));
        }
        if (name.equals("valueOf") && argumentsTypes.size() == 1) {
            ResolvedType argument = argumentsTypes.get(0);
            if (argument.isReferenceType() && "java.lang.String".equals(argument.asReferenceType().getQualifiedName())) {
                return SymbolReference.solved(new JavaParserEnumDeclaration.ValueOfMethod(this, typeSolver));
            }
        }
        return getContext().solveMethod(name, argumentsTypes, staticOnly);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return getContext().solveSymbol(name);
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        List<ResolvedFieldDeclaration> fields = javaParserTypeAdapter.getFieldsForDeclaredVariables();

        this.getAncestors().forEach(a -> fields.addAll(a.getAllFieldsVisibleToInheritors()));

        this.wrappedNode.getMembers().stream().filter(m -> m instanceof FieldDeclaration).forEach(m -> {
                FieldDeclaration fd = (FieldDeclaration)m;
                fd.getVariables().forEach(v -> fields.add(new JavaParserFieldDeclaration(v, typeSolver)));
        });

        return fields;
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();

        ResolvedReferenceType enumClass = ReflectionFactory.typeUsageFor(Enum.class, typeSolver).asReferenceType();
        if(enumClass.getTypeDeclaration().isPresent()) {
            ResolvedTypeParameterDeclaration eTypeParameter = enumClass.getTypeDeclaration().get()
                    .getTypeParameters()
                    .get(0);
            enumClass = enumClass.deriveTypeParameters(new ResolvedTypeParametersMap.Builder()
                    .setValue(eTypeParameter, new ReferenceTypeImpl(this))
                    .build());
            ancestors.add(enumClass);
        } else {
            // Consider IllegalStateException or similar?
        }

        // TODO FIXME: Remove null check -- should be an empty list...
        if (wrappedNode.getImplementedTypes() != null) {
            for (ClassOrInterfaceType implementedType : wrappedNode.getImplementedTypes()) {
                try {
                    ancestors.add(toReferenceType(implementedType));
                } catch (UnsolvedSymbolException e) {
                    if (!acceptIncompleteList) {
                        throw e;
                    }
                }
            }
        }

        return ancestors;
    }

    private ResolvedReferenceType toReferenceType(ClassOrInterfaceType classOrInterfaceType) {
        String className = classOrInterfaceType.getName().getId();
        if (classOrInterfaceType.getScope().isPresent()) {
            // look for the qualified name (for example class of type Rectangle2D.Double)
            className = classOrInterfaceType.getScope().get().toString() + "." + className;
        }
        SymbolReference<ResolvedTypeDeclaration> ref = solveType(className);
        if (!ref.isSolved()) {
            throw new UnsolvedSymbolException(classOrInterfaceType.getName().getId());
        }
        if (!classOrInterfaceType.getTypeArguments().isPresent()) {
            return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType());
        }
        List<ResolvedType> superClassTypeParameters = classOrInterfaceType.getTypeArguments().get()
                .stream().map(ta -> new LazyType(v -> JavaParserFacade.get(typeSolver).convert(ta, ta)))
                .collect(Collectors.toList());
        return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType(), superClassTypeParameters);
    }

    /**
     * This method is deprecated because it receives the TypesSolver as a parameter.
     * Eventually we would like to remove all usages of TypeSolver as a parameter.
     *
     * Also, resolution should move out of declarations, so that they are pure declarations and the resolution should
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

        return getContext().getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveType(name);
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }

    /**
     * Returns the JavaParser node associated with this JavaParserEnumDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public com.github.javaparser.ast.body.EnumDeclaration getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public List<ResolvedEnumConstantDeclaration> getEnumConstants() {
        return wrappedNode.getEntries().stream()
                .map(entry -> new JavaParserEnumConstantDeclaration(entry, typeSolver))
                .collect(Collectors.toList());
    }

    /**
     * Needed by ContextHelper
     *
     * An implicitly declared method {@code public static E[] values()}, which returns an array containing the
     * enum constants of {@code E}, in the same order as they appear in the body of the declaration of E.
     *
     * @see <a href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-8.html#jls-8.9.2">https://docs.oracle.com/javase/specs/jls/se7/html/jls-8.html#jls-8.9.2</a>
     * @see <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-8.html#jls-8.9.3">https://docs.oracle.com/javase/specs/jls/se8/html/jls-8.html#jls-8.9.3</a>
     * @see <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-14.html#jls-8.9.3">https://docs.oracle.com/javase/specs/jls/se8/html/jls-14.html#jls-8.9.3</a>
     */
    public static class ValuesMethod implements ResolvedMethodDeclaration, TypeVariableResolutionCapability {

        private JavaParserEnumDeclaration enumDeclaration;
        private TypeSolver typeSolver;

        public ValuesMethod(JavaParserEnumDeclaration enumDeclaration, TypeSolver typeSolver) {
            this.enumDeclaration = enumDeclaration;
            this.typeSolver = typeSolver;
        }

        @Override
        public ResolvedReferenceTypeDeclaration declaringType() {
            return enumDeclaration;
        }

        @Override
        public ResolvedType getReturnType() {
            return new ResolvedArrayType(new ReferenceTypeImpl(enumDeclaration));
        }

        @Override
        public int getNumberOfParams() {
            return 0;
        }

        @Override
        public ResolvedParameterDeclaration getParam(int i) {
            throw new UnsupportedOperationException();
        }

        public MethodUsage getUsage(Node node) {
            throw new UnsupportedOperationException();
        }

        public MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes) {
            return new MethodUsage(this);
        }

        @Override
        public boolean isAbstract() {
            throw new UnsupportedOperationException();
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
        public String getName() {
            return "values";
        }

        @Override
        public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
            return Collections.emptyList();
        }

        @Override
        public AccessSpecifier accessSpecifier() {
            return enumDeclaration.getWrappedNode().getAccessSpecifier();
        }

        @Override
        public int getNumberOfSpecifiedExceptions() {
            return 0;
        }

        @Override
        public ResolvedType getSpecifiedException(int index) {
            throw new UnsupportedOperationException("The values method of an enum does not throw any exception");
        }

        @Override
        public Optional<Node> toAst() {
            return enumDeclaration.toAst();
        }

        @Override
        public String toDescriptor() {
            return String.format("()%s", getReturnType().toDescriptor());
        }
    }

    /**
     * Needed by ContextHelper
     * An implicitly declared method {@code public static E valueOf(String name)}, which returns the
     * enum constant of {@code E} with the specified name.
     *
     * @see <a href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-8.html#jls-8.9.2">https://docs.oracle.com/javase/specs/jls/se7/html/jls-8.html#jls-8.9.2</a>
     * @see <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-8.html#jls-8.9.3">https://docs.oracle.com/javase/specs/jls/se8/html/jls-8.html#jls-8.9.3</a>
     * @see <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-14.html#jls-8.9.3">https://docs.oracle.com/javase/specs/jls/se8/html/jls-14.html#jls-8.9.3</a>
     */
    public static class ValueOfMethod implements ResolvedMethodDeclaration, TypeVariableResolutionCapability {

        private JavaParserEnumDeclaration enumDeclaration;
        private TypeSolver typeSolver;

        public ValueOfMethod(JavaParserEnumDeclaration enumDeclaration, TypeSolver typeSolver) {
            this.enumDeclaration = enumDeclaration;
            this.typeSolver = typeSolver;
        }

        @Override
        public ResolvedReferenceTypeDeclaration declaringType() {
            return enumDeclaration;
        }

        @Override
        public ResolvedType getReturnType() {
            return new ReferenceTypeImpl(enumDeclaration);
        }

        @Override
        public int getNumberOfParams() {
            return 1;
        }

        @Override
        public ResolvedParameterDeclaration getParam(int i) {
            if (i == 0) {
                return new ResolvedParameterDeclaration() {

                    @Override
                    public String getName() {
                        return "name";
                    }

                    @Override
                    public ResolvedType getType() {
                        return new ReferenceTypeImpl(typeSolver.solveType("java.lang.String"));
                    }

                    @Override
                    public boolean isVariadic() {
                        return false;
                    }

                    @Override
                    public Optional<Node> toAst() {
                        return enumDeclaration.toAst();
                    }

                };
            }

            throw new IllegalArgumentException("Invalid parameter index!");
        }

        public MethodUsage getUsage(Node node) {
            throw new UnsupportedOperationException();
        }

        @Override
        public MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes) {
            return new MethodUsage(this);
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
            return true;
        }

        @Override
        public String getName() {
            return "valueOf";
        }

        @Override
        public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
            return Collections.emptyList();
        }

        @Override
        public AccessSpecifier accessSpecifier() {
            return AccessSpecifier.PUBLIC;
        }

        @Override
        public int getNumberOfSpecifiedExceptions() {
            return 0;
        }

        @Override
        public ResolvedType getSpecifiedException(int index) {
            throw new UnsupportedOperationException("The valueOf method of an enum does not throw any exception");
        }

        @Override
        public Optional<Node> toAst() {
            return enumDeclaration.toAst();
        }

        @Override
        public String toDescriptor() {
            return String.format("(Ljava/lang/String;)%s", getReturnType().toDescriptor());
        }
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return wrappedNode.getAccessSpecifier();
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        return javaParserTypeAdapter.internalTypes();
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return javaParserTypeAdapter.containerType();
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return AstResolutionUtils.getConstructors(this.wrappedNode, typeSolver, this);
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.of(wrappedNode);
    }

}
