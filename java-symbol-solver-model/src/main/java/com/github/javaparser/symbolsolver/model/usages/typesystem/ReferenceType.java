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

package com.github.javaparser.symbolsolver.model.usages.typesystem;

import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.usages.MethodUsage;
import com.github.javaparser.symbolsolver.model.usages.TypeParametersMap;
import com.github.javaparser.symbolsolver.model.usages.TypeParametrized;
import com.github.javaparser.symbolsolver.model.usages.TypeTransformer;
import javaslang.Tuple2;

import java.util.*;
import java.util.stream.Collectors;

/**
 * A ReferenceType like a class, an interface or an enum. Note that this type can contain also the values
 * specified for the type parameters.
 *
 * @author Federico Tomassetti
 */
public abstract class ReferenceType implements Type, TypeParametrized {

    //
    // Fields
    //

    protected TypeDeclaration typeDeclaration;
    protected TypeSolver typeSolver;
    protected TypeParametersMap typeParametersMap;

    //
    // Constructors
    //

    public ReferenceType(TypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        this(typeDeclaration, deriveParams(typeDeclaration), typeSolver);
    }

    public ReferenceType(TypeDeclaration typeDeclaration, List<Type> typeParameters, TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("typeSolver should not be null");
        }
        if (typeDeclaration.isTypeParameter()) {
            throw new IllegalArgumentException("You should use only Classes, Interfaces and enums");
        }
        if (typeParameters.size() > 0 && typeParameters.size() != typeDeclaration.getTypeParameters().size()) {
            throw new IllegalArgumentException(String.format("expected either zero type parameters or has many as defined in the declaration (%d). Found %d",
                    typeDeclaration.getTypeParameters().size(), typeParameters.size()));
        }
        this.typeParametersMap = new TypeParametersMap();
        for (int i = 0; i < typeParameters.size(); i++) {
            this.typeParametersMap.setValue(typeDeclaration.getTypeParameters().get(i), typeParameters.get(i));
        }
        this.typeDeclaration = typeDeclaration;
        this.typeSolver = typeSolver;
    }

    //
    // Public Object methods
    //

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReferenceType that = (ReferenceType) o;

        if (!typeDeclaration.equals(that.typeDeclaration)) return false;
        if (!typeParametersMap.equals(that.typeParametersMap)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = typeDeclaration.hashCode();
        result = 31 * result + typeParametersMap.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "ReferenceTypeUsage{" +
                "declaration=" + typeDeclaration +
                ", typeParametersMap=" + typeParametersMap +
                '}';
    }

    ///
    /// Relation with other types
    ///

    @Override
    public final boolean isReferenceType() {
        return true;
    }

    ///
    /// Downcasting
    ///

    @Override
    public ReferenceType asReferenceType() {
        return this;
    }

    ///
    /// Naming
    ///

    @Override
    public String describe() {
        StringBuilder sb = new StringBuilder();
        if (hasName()) {
            sb.append(typeDeclaration.getQualifiedName());
        } else {
            sb.append("<anonymous class>");
        }
        if (!typeParametersMap().isEmpty()) {
            sb.append("<");
            sb.append(String.join(", ", typeDeclaration.getTypeParameters().stream()
                    .map(tp -> typeParametersMap().getValue(tp).describe())
                    .collect(Collectors.toList())));
            sb.append(">");
        }
        return sb.toString();
    }

    ///
    /// TypeParameters
    ///

    public Type transformTypeParameters(TypeTransformer transformer) {
        Type result = this;
        int i = 0;
        for (Type tp : this.typeParametersValues()) {
            Type transformedTp = transformer.transform(tp);
            // Identity comparison on purpose
            if (transformedTp != tp) {
                result = result.asReferenceType().replaceParam(i, transformedTp);
            }
            i++;
        }
        return result;
    }

    @Override
    public Type replaceParam(TypeParameterDeclaration tpToReplace, Type replaced) {
        if (replaced == null) {
            throw new IllegalArgumentException();
        }
        return transformTypeParameters(tp -> tp.replaceParam(tpToReplace, replaced));
    }

    ///
    /// Assignability
    ///

    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    @Override
    public abstract boolean isAssignableBy(Type other);

    ///
    /// Ancestors
    ///

    /**
     * Return all ancestors, that means all superclasses and interfaces.
     * This list should always include Object (unless this is a reference to Object).
     * The type typeParametersValues should be expressed in terms of this type typeParametersValues.
     * <p>
     * For example, given:
     * <p>
     * class Foo&lt;A, B&gt; {}
     * class Bar&lt;C&gt; extends Foo&lt;C, String&gt; {}
     * <p>
     * a call to getAllAncestors on a reference to Bar having type parameter Boolean should include
     * Foo&lt;Boolean, String&gt;.
     */
    public List<ReferenceType> getAllAncestors() {
        List<ReferenceType> ancestors = typeDeclaration.getAllAncestors();

        TypeDeclaration objectType = typeSolver.solveType(Object.class.getCanonicalName());
        ReferenceType objectRef = create(objectType, typeSolver);

        ancestors = ancestors.stream()
                .map((a) -> replaceTypeParams(a).asReferenceType())
                .collect(Collectors.toList());

        ancestors.removeIf(a -> a.getQualifiedName().equals(Object.class.getCanonicalName()));
        ancestors.add(objectRef);
        return ancestors;
    }

    public List<ReferenceType> getAllInterfacesAncestors() {
        return getAllAncestors().stream()
                .filter(it -> it.getTypeDeclaration().isInterface())
                .collect(Collectors.toList());
    }

    ///
    /// Type parameters
    ///

    /**
     * Get the type associated with the type parameter with the given name.
     * It returns Optional.empty unless the type declaration declares a type parameter with the given name.
     */
    public Optional<Type> getGenericParameterByName(String name) {
        for (TypeParameterDeclaration tp : typeDeclaration.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(this.typeParametersMap().getValue(tp));
            }
        }
        return Optional.empty();
    }

    /**
     * Replace the type typeParametersValues present in the given type with the ones for which this type
     * has a value.
     */
    @Deprecated
    public Type replaceTypeParams(Type type) {
        if (type.isTypeVariable()) {
            TypeParameterDeclaration typeParameter = type.asTypeParameter();
            if (typeParameter.declaredOnType()) {
                Optional<Type> typeParam = typeParamByName(typeParameter.getName());
                if (typeParam.isPresent()) {
                    type = typeParam.get();
                }
            }
        }

        if (type.isReferenceType()) {
            type = type.asReferenceType().transformTypeParameters(tp -> replaceTypeParams(tp));
        }

        return type;
    }

    public List<Type> typeParametersValues() {
        return this.typeParametersMap.isEmpty() ? Collections.emptyList() : typeDeclaration.getTypeParameters().stream().map(tp -> typeParametersMap.getValue(tp)).collect(Collectors.toList());
    }

    public List<Tuple2<TypeParameterDeclaration, Type>> getTypeParametersMap() {
        List<Tuple2<TypeParameterDeclaration, Type>> typeParametersMap = new ArrayList<>();
        for (int i = 0; i < typeDeclaration.getTypeParameters().size(); i++) {
            typeParametersMap.add(new Tuple2<>(typeDeclaration.getTypeParameters().get(0), typeParametersValues().get(i)));
        }
        return typeParametersMap;
    }

    @Override
    public TypeParametersMap typeParametersMap() {
        return typeParametersMap;
    }

    ///
    /// Other methods introduced by ReferenceType
    ///

    public final TypeDeclaration getTypeDeclaration() {
        return typeDeclaration;
    }

    /**
     * The type of the field could be different from the one in the corresponding FieldDeclaration because
     * type variables would be solved.
     */
    public Optional<Type> getFieldType(String name) {
        if (!typeDeclaration.hasField(name)) {
            return Optional.empty();
        }
        Type type = typeDeclaration.getField(name).getType();
        type = replaceTypeParams(type);
        return Optional.of(type);
    }

    public boolean hasName() {
        return typeDeclaration.hasName();
    }

    public String getQualifiedName() {
        return typeDeclaration.getQualifiedName();
    }

    public abstract Set<MethodUsage> getDeclaredMethods();

    public boolean isRawType() {
        return (!typeDeclaration.getTypeParameters().isEmpty() &&
                typeParametersMap().isEmpty());
    }

    //
    // Protected methods
    //

    protected abstract ReferenceType create(TypeDeclaration typeDeclaration, List<Type> typeParameters, TypeSolver typeSolver);
    protected ReferenceType create(TypeDeclaration typeDeclaration, TypeParametersMap typeParametersMap, TypeSolver typeSolver) {
        return create(typeDeclaration, typeDeclaration.getTypeParameters().stream()
                .map(tp -> typeParametersMap.getValue(tp))
                .collect(Collectors.toList()), typeSolver);
    }
    protected abstract ReferenceType create(TypeDeclaration typeDeclaration, TypeSolver typeSolver);

    protected boolean isCorrespondingBoxingType(String typeName) {
        switch (typeName) {
            case "boolean":
                return getQualifiedName().equals(Boolean.class.getCanonicalName());
            case "char":
                return getQualifiedName().equals(Character.class.getCanonicalName());
            case "byte":
                return getQualifiedName().equals(Byte.class.getCanonicalName());
            case "short":
                return getQualifiedName().equals(Short.class.getCanonicalName());
            case "int":
                return getQualifiedName().equals(Integer.class.getCanonicalName());
            case "long":
                return getQualifiedName().equals(Long.class.getCanonicalName());
            case "float":
                return getQualifiedName().equals(Float.class.getCanonicalName());
            case "double":
                return getQualifiedName().equals(Double.class.getCanonicalName());
            default:
                throw new UnsupportedOperationException(typeName);
        }
    }

    protected boolean compareConsideringTypeParameters(ReferenceType other) {
        if (other.equals(this)) {
            return true;
        }
        if (this.getQualifiedName().equals(other.getQualifiedName())) {
            if (this.isRawType() || other.isRawType()) {
                return true;
            }
            if (this.typeParametersValues().size() != other.typeParametersValues().size()) {
                throw new IllegalStateException();
            }
            for (int i = 0; i < typeParametersValues().size(); i++) {
                Type thisParam = typeParametersValues().get(i);
                Type otherParam = other.typeParametersValues().get(i);
                if (!thisParam.equals(otherParam)) {
                    if (thisParam instanceof Wildcard) {
                        Wildcard thisParamAsWildcard = (Wildcard) thisParam;
                        if (thisParamAsWildcard.isSuper() && otherParam.isAssignableBy(thisParamAsWildcard.getBoundedType())) {
                            // ok
                        } else if (thisParamAsWildcard.isExtends() && thisParamAsWildcard.getBoundedType().isAssignableBy(otherParam)) {
                            // ok
                        } else {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            }
            return true;
        }
        return false;
    }

    //
    // Private methods
    //

    private static List<Type> deriveParams(TypeDeclaration typeDeclaration) {
        return typeDeclaration.getTypeParameters().stream().map((tp) -> new TypeVariable(tp)).collect(Collectors.toList());
    }

    @Deprecated
    private Optional<Type> typeParamByName(String name) {
        List<Type> typeParameters = this.typeParametersValues();
        TypeDeclaration objectType = typeSolver.solveType(Object.class.getCanonicalName());
        ReferenceType objectRef = create(objectType, typeSolver);
        if (typeDeclaration.getTypeParameters().size() != typeParameters.size()) {
            if (!typeParameters.isEmpty()) {
                throw new UnsupportedOperationException();
            }
            // type typeParametersValues not specified, default to Object
            typeParameters = new ArrayList<>();
            for (int i = 0; i < typeDeclaration.getTypeParameters().size(); i++) {
                typeParameters.add(objectRef);
            }
        }
        int i = 0;
        for (TypeParameterDeclaration tp : typeDeclaration.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(typeParameters.get(i));
            }
            i++;
        }
        return Optional.empty();
    }

    /**
     * Create a copy of the value with the type parameter changed.
     */
    @Deprecated
    private Type replaceParam(int i, Type replaced) {
        List<Type> typeParametersCorrected = typeParametersValues();
        typeParametersCorrected.set(i, replaced);
        return create(typeDeclaration, typeParametersCorrected, typeSolver);
    }

}
