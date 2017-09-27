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

package com.github.javaparser.resolution.types;

import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParameterValueProvider;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametrized;
import com.github.javaparser.utils.Pair;

import java.util.*;
import java.util.stream.Collectors;

/**
 * A ReferenceType like a class, an interface or an enum. Note that this type can contain also the values
 * specified for the type parameters.
 *
 * @author Federico Tomassetti
 */
public abstract class ResolvedReferenceType implements ResolvedType,
        ResolvedTypeParametrized, ResolvedTypeParameterValueProvider {

    //
    // Fields
    //

    protected ResolvedReferenceTypeDeclaration typeDeclaration;
    protected ResolvedTypeParametersMap typeParametersMap;

    //
    // Constructors
    //

    public ResolvedReferenceType(ResolvedReferenceTypeDeclaration typeDeclaration, List<ResolvedType> typeArguments) {
        if (typeDeclaration.isTypeParameter()) {
            throw new IllegalArgumentException("You should use only Classes, Interfaces and enums");
        }
        if (typeArguments.size() > 0 && typeArguments.size() != typeDeclaration.getTypeParameters().size()) {
            throw new IllegalArgumentException(String.format(
                    "expected either zero type arguments or has many as defined in the declaration (%d). Found %d",
                    typeDeclaration.getTypeParameters().size(), typeArguments.size()));
        }
        ResolvedTypeParametersMap.Builder typeParametersMapBuilder = new ResolvedTypeParametersMap.Builder();
        for (int i = 0; i < typeArguments.size(); i++) {
            typeParametersMapBuilder.setValue(typeDeclaration.getTypeParameters().get(i), typeArguments.get(i));
        }
        this.typeParametersMap = typeParametersMapBuilder.build();
        this.typeDeclaration = typeDeclaration;
    }

    //
    // Public Object methods
    //

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ResolvedReferenceType that = (ResolvedReferenceType) o;

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
        return "ReferenceType{" + getQualifiedName() +
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
    public ResolvedReferenceType asReferenceType() {
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

    /**
     * Execute a transformation on all the type parameters of this element.
     */
    public abstract ResolvedType transformTypeParameters(ResolvedTypeTransformer transformer);

    ///
    /// Assignability
    ///

    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    @Override
    public abstract boolean isAssignableBy(ResolvedType other);

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
    public abstract List<ResolvedReferenceType> getAllAncestors();

    public final List<ResolvedReferenceType> getAllInterfacesAncestors() {
        return getAllAncestors().stream()
                .filter(it -> it.getTypeDeclaration().isInterface())
                .collect(Collectors.toList());
    }

    public final List<ResolvedReferenceType> getAllClassesAncestors() {
        return getAllAncestors().stream()
                .filter(it -> it.getTypeDeclaration().isClass())
                .collect(Collectors.toList());
    }

    ///
    /// Type parameters
    ///

    /**
     * Get the type associated with the type parameter with the given name.
     * It returns Optional.empty unless the type declaration declares a type parameter with the given name.
     */
    public Optional<ResolvedType> getGenericParameterByName(String name) {
        for (ResolvedTypeParameterDeclaration tp : typeDeclaration.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(this.typeParametersMap().getValue(tp));
            }
        }
        return Optional.empty();
    }

    /**
     * Get the values for all type parameters declared on this type.
     * The list can be empty for raw types.
     */
    public List<ResolvedType> typeParametersValues() {
        return this.typeParametersMap.isEmpty() ? Collections.emptyList() : typeDeclaration.getTypeParameters().stream().map(tp -> typeParametersMap.getValue(tp)).collect(Collectors.toList());
    }

    /**
     * Get the values for all type parameters declared on this type.
     * In case of raw types the values correspond to TypeVariables.
     */
    public List<Pair<ResolvedTypeParameterDeclaration, ResolvedType>> getTypeParametersMap() {
        List<Pair<ResolvedTypeParameterDeclaration, ResolvedType>> typeParametersMap = new ArrayList<>();
        if (!isRawType()) {
	        for (int i = 0; i < typeDeclaration.getTypeParameters().size(); i++) {
	            typeParametersMap.add(new Pair<>(typeDeclaration.getTypeParameters().get(0), typeParametersValues().get(i)));
	        }
        }
        return typeParametersMap;
    }

    @Override
    public ResolvedTypeParametersMap typeParametersMap() {
        return typeParametersMap;
    }

    ///
    /// Other methods introduced by ReferenceType
    ///

    /**
     * Corresponding TypeDeclaration
     */
    public final ResolvedReferenceTypeDeclaration getTypeDeclaration() {
        return typeDeclaration;
    }

    /**
     * The type of the field could be different from the one in the corresponding FieldDeclaration because
     * type variables would be solved.
     */
    public Optional<ResolvedType> getFieldType(String name) {
        if (!typeDeclaration.hasField(name)) {
            return Optional.empty();
        }
        ResolvedType type = typeDeclaration.getField(name).getType();
        type = useThisTypeParametersOnTheGivenType(type);
        return Optional.of(type);
    }

    /**
     * Has the TypeDeclaration a name? Anonymous classes do not have one.
     */
    public boolean hasName() {
        return typeDeclaration.hasName();
    }

    /**
     * Qualified name of the declaration.
     */
    public String getQualifiedName() {
        return typeDeclaration.getQualifiedName();
    }

    /**
     * Id of the declaration. It corresponds to the qualified name, unless for local classes.
     */
    public String getId() {
        return typeDeclaration.getId();
    }

    /**
     * Methods declared on this type.
     */
    public abstract Set<MethodUsage> getDeclaredMethods();

    public boolean isRawType() {
        if (!typeDeclaration.getTypeParameters().isEmpty()) {
            if (typeParametersMap().isEmpty()) {
                return true;
            }
            for (String name : typeParametersMap().getNames()) {
                Optional<ResolvedType> value = typeParametersMap().getValueBySignature(name);
                if (value.isPresent() && value.get().isTypeVariable() && value.get().asTypeVariable().qualifiedName().equals(name)) {
                    // nothing to do
                } else {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    public Optional<ResolvedType> typeParamValue(ResolvedTypeParameterDeclaration typeParameterDeclaration) {
        if (typeParameterDeclaration.declaredOnMethod()) {
            throw new IllegalArgumentException();
        }
        String typeId = this.getTypeDeclaration().getId();
        if (typeId.equals(typeParameterDeclaration.getContainerId())) {
            return Optional.of(this.typeParametersMap().getValue(typeParameterDeclaration));
        }
        for (ResolvedReferenceType ancestor : this.getAllAncestors()) {
            if (ancestor.getId().equals(typeParameterDeclaration.getContainerId())) {
                return Optional.of(ancestor.typeParametersMap().getValue(typeParameterDeclaration));
            }
        }
        return Optional.empty();
    }

    public abstract ResolvedType toRawType();

    //
    // Protected methods
    //

    protected abstract ReferenceType create(ResolvedReferenceTypeDeclaration typeDeclaration, List<ResolvedType> typeParameters);

    protected ReferenceType create(ResolvedReferenceTypeDeclaration typeDeclaration, ResolvedTypeParametersMap typeParametersMap) {
        return create(typeDeclaration, typeDeclaration.getTypeParameters().stream()
                .map(typeParametersMap::getValue)
                .collect(Collectors.toList()));
    }

    protected abstract ReferenceType create(ResolvedReferenceTypeDeclaration typeDeclaration);

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

    protected boolean compareConsideringTypeParameters(ResolvedReferenceType other) {
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
                ResolvedType thisParam = typeParametersValues().get(i);
                ResolvedType otherParam = other.typeParametersValues().get(i);
                if (!thisParam.equals(otherParam)) {
                    if (thisParam instanceof ResolvedWildcard) {
                        ResolvedWildcard thisParamAsWildcard = (ResolvedWildcard) thisParam;
                        if (thisParamAsWildcard.isSuper() && otherParam.isAssignableBy(thisParamAsWildcard.getBoundedType())) {
                            // ok
                        } else if (thisParamAsWildcard.isExtends() && thisParamAsWildcard.getBoundedType().isAssignableBy(otherParam)) {
                            // ok
                        } else if (!thisParamAsWildcard.isBounded()) {
                            // ok
                        } else {
                            return false;
                        }
                    } else {
                        if (thisParam instanceof ResolvedTypeVariable && otherParam instanceof ResolvedTypeVariable) {
                            List<ResolvedType> thisBounds = thisParam.asTypeVariable().asTypeParameter().getBounds().stream().map(bound -> bound.getType()).collect(Collectors.toList());
                            List<ResolvedType> otherBounds = otherParam.asTypeVariable().asTypeParameter().getBounds().stream().map(bound -> bound.getType()).collect(Collectors.toList());
                            if (thisBounds.size() == otherBounds.size() && otherBounds.containsAll(thisBounds)) {
                                return true;
                            }
                        }
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

    private static List<ResolvedType> deriveParams(ResolvedReferenceTypeDeclaration typeDeclaration) {
        return typeDeclaration.getTypeParameters().stream().map((tp) -> new ResolvedTypeVariable(tp)).collect(Collectors.toList());
    }

    public abstract ReferenceType deriveTypeParameters(ResolvedTypeParametersMap typeParametersMap);
}
