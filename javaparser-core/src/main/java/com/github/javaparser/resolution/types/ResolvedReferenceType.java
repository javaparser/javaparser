/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
package com.github.javaparser.resolution.types;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration.Bound;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParameterValueProvider;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametrized;
import com.github.javaparser.utils.Pair;

/**
 * A ReferenceType like a class, an interface or an enum. Note that this type can contain also the values
 * specified for the type parameters.
 *
 * @author Federico Tomassetti
 */
public abstract class ResolvedReferenceType implements ResolvedType, ResolvedTypeParametrized, ResolvedTypeParameterValueProvider {

    protected static String JAVA_LANG_ENUM = java.lang.Enum.class.getCanonicalName();

    protected static String JAVA_LANG_OBJECT = java.lang.Object.class.getCanonicalName();

    //
    // Fields
    //
    protected ResolvedReferenceTypeDeclaration typeDeclaration;

    protected ResolvedTypeParametersMap typeParametersMap;

    //
    // Constructors
    //
    public ResolvedReferenceType(ResolvedReferenceTypeDeclaration typeDeclaration) {
        this(typeDeclaration, deriveParams(typeDeclaration));
    }

    public ResolvedReferenceType(ResolvedReferenceTypeDeclaration typeDeclaration, List<ResolvedType> typeArguments) {
        if (typeDeclaration == null) {
            throw new IllegalArgumentException("TypeDeclaration is not expected to be null");
        }
        if (typeDeclaration.isTypeParameter()) {
            throw new IllegalArgumentException("You should use only Classes, Interfaces and enums");
        }
        if (typeArguments.size() > 0 && typeArguments.size() != typeDeclaration.getTypeParameters().size()) {
            throw new IllegalArgumentException(String.format("expected either zero type arguments or has many as defined in the declaration (%d). Found %d", typeDeclaration.getTypeParameters().size(), typeArguments.size()));
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
        if (this == o)
            return true;
        if (o == null || (!isLazyType(o) && getClass() != o.getClass())
        		|| (isLazyType(o) && !this.equals(asResolvedReferenceType(o))))
            return false;
        ResolvedReferenceType that = asResolvedReferenceType(o);
        if (!typeDeclaration.equals(that.typeDeclaration))
            return false;
        if (!typeParametersMap.equals(that.typeParametersMap))
            return false;
        return true;
    }

    private boolean isLazyType(Object type) {
    	return type !=null && type instanceof LazyType;
    }

    private ResolvedReferenceType asResolvedReferenceType(Object o) {
    	if (isLazyType(o)) {
    		return ((LazyType) o).asReferenceType();
    	}
    	return ResolvedReferenceType.class.cast(o);
    }

    @Override
    public int hashCode() {
        int result = typeDeclaration.hashCode();
        result = 31 * result + typeParametersMap.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "ReferenceType{" + getQualifiedName() + ", typeParametersMap=" + typeParametersMap + '}';
    }

    // /
    // / Relation with other types
    // /
    @Override
    public final boolean isReferenceType() {
        return true;
    }

    // /
    // / Downcasting
    // /
    @Override
    public ResolvedReferenceType asReferenceType() {
        return this;
    }

    // /
    // / Naming
    // /
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
            sb.append(String.join(", ", typeDeclaration.getTypeParameters().stream().map(tp -> typeParametersMap().getValue(tp).describe()).collect(Collectors.toList())));
            sb.append(">");
        }
        return sb.toString();
    }

    // /
    // / TypeParameters
    // /
    /**
     * Execute a transformation on all the type parameters of this element.
     */
    public abstract ResolvedType transformTypeParameters(ResolvedTypeTransformer transformer);

    @Override
    public ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tpToReplace, ResolvedType replaced, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        if (replaced == null) {
            throw new IllegalArgumentException();
        }
        ResolvedReferenceType result = this;
        int i = 0;
        for (ResolvedType tp : this.typeParametersValues()) {
            ResolvedType transformedTp = tp.replaceTypeVariables(tpToReplace, replaced, inferredTypes);
            // Identity comparison on purpose
            if (tp.isTypeVariable() && tp.asTypeVariable().describe().equals(tpToReplace.getName())) {
                inferredTypes.put(tp.asTypeParameter(), replaced);
            }
            // FIXME
            if (true) {
                List<ResolvedType> typeParametersCorrected = result.asReferenceType().typeParametersValues();
                typeParametersCorrected.set(i, transformedTp);
                result = create(typeDeclaration, typeParametersCorrected);
            }
            i++;
        }
        List<ResolvedType> values = result.typeParametersValues();
        // FIXME
        if (values.contains(tpToReplace)) {
            int index = values.indexOf(tpToReplace);
            values.set(index, replaced);
            if (result.getTypeDeclaration().isPresent()) {
                return create(result.getTypeDeclaration().get(), values);
            }
        }
        return result;
    }

    // /
    // / Assignability
    // /
    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    @Override
    public abstract boolean isAssignableBy(ResolvedType other);

    // /
    // / Ancestors
    // /
    /**
     * Return all ancestors, that means all superclasses and interfaces.
     * This list should always include Object (unless this is a reference to Object).
     * The type typeParametersValues should be expressed in terms of this type typeParametersValues.
     * The default order of presenting ancestors corresponds to a search in depth.
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

    /**
     * Return all ancestors, that means all superclasses and interfaces.
     * This list should always include Object (unless this is a reference to Object).
     * The type typeParametersValues should be expressed in terms of this type typeParametersValues.
     */
    public abstract List<ResolvedReferenceType> getAllAncestors(Function<ResolvedReferenceTypeDeclaration, List<ResolvedReferenceType>> traverser);

    /**
     * Return direct ancestors, that means the superclasses and interfaces implemented directly.
     * This list should include Object if the class has no other superclass or the interface is not extending another interface.
     * There is an exception for Object itself.
     */
    public abstract List<ResolvedReferenceType> getDirectAncestors();

    public final List<ResolvedReferenceType> getAllInterfacesAncestors() {
        return getAllAncestors().stream().filter(it -> it.getTypeDeclaration().isPresent()).filter(it -> it.getTypeDeclaration().get().isInterface()).collect(Collectors.toList());
    }

    public final List<ResolvedReferenceType> getAllClassesAncestors() {
        return getAllAncestors().stream().filter(it -> it.getTypeDeclaration().isPresent()).filter(it -> it.getTypeDeclaration().get().isClass()).collect(Collectors.toList());
    }

    // /
    // / Type parameters
    // /
    /**
     * Get the type associated with the type parameter with the given name.
     * It returns Optional.empty unless the type declaration declares a type parameter with the given name.
     */
    @Override
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
                typeParametersMap.add(new Pair<>(typeDeclaration.getTypeParameters().get(i), typeParametersValues().get(i)));
            }
        }
        return typeParametersMap;
    }

    @Override
    public ResolvedTypeParametersMap typeParametersMap() {
        return typeParametersMap;
    }

    // /
    // / Other methods introduced by ReferenceType
    // /
    /**
     * Corresponding TypeDeclaration
     */
    public final Optional<ResolvedReferenceTypeDeclaration> getTypeDeclaration() {
        return Optional.of(typeDeclaration);
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

    /**
     * Fields declared on this type.
     */
    public abstract Set<ResolvedFieldDeclaration> getDeclaredFields();

    public boolean isRawType() {
        if (!typeDeclaration.getTypeParameters().isEmpty()) {
            if (typeParametersMap().isEmpty()) {
                return true;
            }
            for (String name : typeParametersMap().getNames()) {
                Optional<ResolvedType> value = typeParametersMap().getValueBySignature(name);
                if (!value.isPresent() || !value.get().isTypeVariable() || !value.get().asTypeVariable().qualifiedName().equals(name)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    @Override
	public Optional<ResolvedType> typeParamValue(ResolvedTypeParameterDeclaration typeParameterDeclaration) {
        if (typeParameterDeclaration.declaredOnMethod()) {
            throw new IllegalArgumentException();
        }
        if (!this.getTypeDeclaration().isPresent()) {
            // TODO: Consider IllegalStateException or similar
            return Optional.empty();
        }
        String typeId = this.getTypeDeclaration().get().getId();
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

    /**
     * @return A copy of the current reference type, without type parameters.
     */
    public abstract ResolvedType toRawType();

    /**
     * Get a list of all the methods available on this type. This list includes methods declared in this type and
     * methods inherited. This list includes methods of all sort of visibility. However it does not include methods
     * that have been overwritten.
     */
    public List<ResolvedMethodDeclaration> getAllMethods() {
        if (!this.getTypeDeclaration().isPresent()) {
            // empty list -- consider IllegalStateException or similar
            return new ArrayList<>();
        }
        // Get the methods declared directly on this.
        List<ResolvedMethodDeclaration> allMethods = new LinkedList<>(this.getTypeDeclaration().get().getDeclaredMethods());
        // Also get methods inherited from ancestors.
        getDirectAncestors().forEach(a -> allMethods.addAll(a.getAllMethods()));
        return allMethods;
    }

    /**
     * Fields which are visible to inheritors. They include all inherited fields which are visible to this
     * type plus all declared fields which are not private.
     */
    public List<ResolvedFieldDeclaration> getAllFieldsVisibleToInheritors() {
        List<ResolvedFieldDeclaration> res = new LinkedList<>(this.getDeclaredFields().stream().filter(f -> f.accessSpecifier() != AccessSpecifier.PRIVATE).collect(Collectors.toList()));
        getDirectAncestors().forEach(a -> res.addAll(a.getAllFieldsVisibleToInheritors()));
        return res;
    }

    public List<ResolvedMethodDeclaration> getAllMethodsVisibleToInheritors() {
        return this.getAllMethods().stream().filter(m -> m.accessSpecifier() != AccessSpecifier.PRIVATE).collect(Collectors.toList());
    }

    //
    // Protected methods
    //
    protected abstract ResolvedReferenceType create(ResolvedReferenceTypeDeclaration typeDeclaration, List<ResolvedType> typeParameters);

    protected ResolvedReferenceType create(ResolvedReferenceTypeDeclaration typeDeclaration, ResolvedTypeParametersMap typeParametersMap) {
        return create(typeDeclaration, typeDeclaration.getTypeParameters().stream().map(typeParametersMap::getValue).collect(Collectors.toList()));
    }

    protected abstract ResolvedReferenceType create(ResolvedReferenceTypeDeclaration typeDeclaration);

    /*
     * Verify if the resolved type is a boxing type of a primitive
     */
    protected boolean isCorrespondingBoxingType(String typeName) {
        ResolvedPrimitiveType resolvedPrimitiveType = (ResolvedPrimitiveType) ResolvedPrimitiveType.byName(typeName);
        return getQualifiedName().equals(resolvedPrimitiveType.getBoxTypeQName());
    }

    protected boolean compareConsideringTypeParameters(ResolvedReferenceType other) {
        if (other.equals(this)) {
            return true;
        }
        if (this.getQualifiedName().equals(other.getQualifiedName())) {
            if (this.isRawType() || other.isRawType()) {
                return true;
            }
            List<ResolvedType> typeParametersValues = typeParametersValues();
            if (typeParametersValues.size() != other.typeParametersValues().size()) {
                throw new IllegalStateException();
            }
            for (int i = 0; i < typeParametersValues.size(); i++) {
                ResolvedType thisParam = typeParametersValues.get(i);
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
                            List<ResolvedType> thisBounds = thisParam.asTypeVariable().asTypeParameter().getBounds().stream().map(ResolvedTypeParameterDeclaration.Bound::getType).collect(Collectors.toList());
                            List<ResolvedType> otherBounds = otherParam.asTypeVariable().asTypeParameter().getBounds().stream().map(ResolvedTypeParameterDeclaration.Bound::getType).collect(Collectors.toList());
                            return thisBounds.size() == otherBounds.size() && otherBounds.containsAll(thisBounds);
                        }
                                            if (!(thisParam instanceof ResolvedTypeVariable) && otherParam instanceof ResolvedTypeVariable) {
                            return compareConsideringVariableTypeParameters(thisParam, (ResolvedTypeVariable) otherParam);
                        }
                        if (thisParam instanceof ResolvedTypeVariable && !(otherParam instanceof ResolvedTypeVariable)) {
                            return compareConsideringVariableTypeParameters(otherParam, (ResolvedTypeVariable) thisParam);
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
    private boolean compareConsideringVariableTypeParameters(ResolvedType referenceType, ResolvedTypeVariable typeVariable) {
        // verify if the ResolvedTypeVariable has only one type variable and the bound is
        // not a reference type with a bound parameter
        // for example EnumSet<E> noneOf(Class<E> elementType)
        List<Bound> bounds = typeVariable.asTypeVariable().asTypeParameter().getBounds();
        if (bounds.size() == 1) {
            ResolvedType boundType = bounds.get(0).getType();
            boolean hasTypeParameter = boundType.isReferenceType() && !boundType.asReferenceType().typeParametersMap.isEmpty();
            return hasTypeParameter ? compareConsideringTypeParameters(boundType.asReferenceType()) : boundType.isAssignableBy(referenceType);
        }
        return false;
    }

    private static List<ResolvedType> deriveParams(ResolvedReferenceTypeDeclaration typeDeclaration) {
        if (typeDeclaration == null) {
            throw new IllegalArgumentException("TypeDeclaration is not expected to be null");
        }
        List<ResolvedTypeParameterDeclaration> typeParameters = typeDeclaration.getTypeParameters();
        if (typeParameters == null) {
            throw new RuntimeException("Type parameters are not expected to be null");
        }
        return typeParameters.stream().map(ResolvedTypeVariable::new).collect(Collectors.toList());
    }

    public abstract ResolvedReferenceType deriveTypeParameters(ResolvedTypeParametersMap typeParametersMap);

    /**
     * We don't make this _ex_plicit in the data representation because that would affect codegen
     * and make everything generate like {@code <T extends Object>} instead of {@code <T>}
     *
     * @return true, if this represents {@code java.lang.Object}
     * @see ResolvedReferenceTypeDeclaration#isJavaLangObject()
     * @see <a href="https://github.com/javaparser/javaparser/issues/2044">https://github.com/javaparser/javaparser/issues/2044</a>
     */
    public boolean isJavaLangObject() {
        return this.isReferenceType() && // Consider anonymous classes
        hasName() && getQualifiedName().equals(JAVA_LANG_OBJECT);
    }

    /**
     * @return true, if this represents {@code java.lang.Enum}
     * @see ResolvedReferenceTypeDeclaration#isJavaLangEnum()
     */
    public boolean isJavaLangEnum() {
        return this.isReferenceType() && // Consider anonymous classes
        hasName() && getQualifiedName().equals(JAVA_LANG_ENUM);
    }

    // /
    // / boxing/unboxing capability
    // /
    /*
     * Returns true if the reference type can be unboxed to the primitive type
     * For example : Integer to int
     */
    public boolean isUnboxable() {
        return Arrays.stream(ResolvedPrimitiveType.values()).anyMatch(pt -> getQualifiedName().equals(pt.getBoxTypeQName()));
    }

    /*
     * Returns true if the reference type can be unboxed to the specified primitive type
     * For example : Integer to int
     */
    public boolean isUnboxableTo(ResolvedPrimitiveType primitiveType) {
        return primitiveType.getBoxTypeQName().equals(this.asReferenceType().describe());
    }

    /*
     * Returns the optional corresponding primitive type
     */
    public Optional<ResolvedPrimitiveType> toUnboxedType() {
        return Arrays.stream(ResolvedPrimitiveType.values()).filter(pt -> this.asReferenceType().getQualifiedName().equals(pt.getBoxTypeQName())).findFirst();
    }

    // /
    // / Erasure
    // /
    // The erasure of a parameterized type (§4.5) G<T1,...,Tn> is |G|.
    @Override
    public ResolvedType erasure() {
        if (!typeDeclaration.isGeneric())
            return this;
        return create(typeDeclaration, erasureOfParamaters(typeParametersMap));
    }

    private List<ResolvedType> erasureOfParamaters(ResolvedTypeParametersMap typeParametersMap) {
        List<ResolvedType> erasedParameters = new ArrayList<ResolvedType>();
        if (!typeParametersMap.isEmpty()) {
            // add erased type except java.lang.object
        	List<ResolvedType> parameters = typeParametersMap.getTypes().stream()
        			.filter(type -> !type.isReferenceType())
        			.map(type -> type.erasure())
        			.filter(erasedType -> !(isJavaObject(erasedType)))
        			.filter(erasedType -> erasedType != null)
        			.collect(Collectors.toList());
            erasedParameters.addAll(parameters);
        }
        return erasedParameters;
    }

    private boolean isJavaObject(ResolvedType rt) {
        return rt != null && rt.isReferenceType() && rt.asReferenceType().isJavaLangObject();
    }

    @Override
    public String toDescriptor() {
        return String.format("L%s;", getQualifiedName().replace(".", "/"));
    }
}
