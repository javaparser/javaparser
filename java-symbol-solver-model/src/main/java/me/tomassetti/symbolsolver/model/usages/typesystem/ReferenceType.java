package me.tomassetti.symbolsolver.model.usages.typesystem;

import javaslang.Tuple2;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeParametersMap;
import me.tomassetti.symbolsolver.model.usages.TypeParametrized;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public abstract class ReferenceType implements Type, TypeParametrized {

    protected TypeDeclaration typeDeclaration;
    protected List<Type> typeParameters;
    protected TypeSolver typeSolver;
    protected TypeParametersMap typeParametersMap;

    public ReferenceType(TypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        this(typeDeclaration, deriveParams(typeDeclaration), typeSolver);
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    public ReferenceType(TypeDeclaration typeDeclaration, List<Type> typeParameters, TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("typeSolver should not be null");
        }
        if (typeParameters.size() > 0 && typeParameters.size() != typeDeclaration.getTypeParameters().size()) {
            throw new IllegalArgumentException(String.format("expected either zero type parameters or has many as defined in the declaration (%d). Found %d",
                    typeDeclaration.getTypeParameters().size(), typeParameters.size()));
        }
        this.typeParametersMap = new TypeParametersMap();
        for (int i=0;i<typeParameters.size();i++) {
            this.typeParametersMap.setValue(typeDeclaration.getTypeParameters().get(i), typeParameters.get(i));
        }
        this.typeDeclaration = typeDeclaration;
        this.typeParameters = typeParameters;
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    private static List<Type> deriveParams(TypeDeclaration typeDeclaration) {
        return typeDeclaration.getTypeParameters().stream().map((tp) -> new TypeParameter(tp)).collect(Collectors.toList());
    }

    public ReferenceType asReferenceType() {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReferenceType that = (ReferenceType) o;

        if (!typeDeclaration.equals(that.typeDeclaration)) return false;
        if (!typeParameters.equals(that.typeParameters)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = typeDeclaration.hashCode();
        result = 31 * result + typeParameters.hashCode();
        return result;
    }

    public final TypeDeclaration getTypeDeclaration() {
        return typeDeclaration;
    }

    @Override
    public final boolean isArray() {
        return false;
    }

    @Override
    public final boolean isPrimitive() {
        return false;
    }

    @Override
    public final boolean isReferenceType() {
        return true;
    }

    @Override
    public String toString() {
        return "ReferenceTypeUsage{" +
                "declaration=" + typeDeclaration +
                ", typeParametersValues=" + typeParameters +
                '}';
    }

    protected abstract ReferenceType create(TypeDeclaration typeDeclaration, TypeSolver typeSolver);

    @Deprecated
    private Optional<Type> typeParamByName(String name) {
        List<Type> typeParameters = this.typeParameters;
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

    /**
     * Get the type associated with the type parameter with the given name.
     * It returns Optional.empty unless the type declaration declares a type parameter with the given name.
     */
    @Deprecated
    public Optional<Type> getGenericParameterByName(String name) {
        int i = 0;
        for (TypeParameterDeclaration tp : typeDeclaration.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(this.typeParameters.get(i));
            }
            i++;
        }
        return Optional.empty();
    }

    /**
     * Create a copy of the value with the type parameter changed.
     */
    @Deprecated
    public Type replaceParam(int i, Type replaced) {
        ArrayList<Type> typeParametersCorrected = new ArrayList<>(typeParameters);
        typeParametersCorrected.set(i, replaced);
        return create(typeDeclaration, typeParametersCorrected, typeSolver);
    }

    protected abstract ReferenceType create(TypeDeclaration typeDeclaration, List<Type> typeParametersCorrected, TypeSolver typeSolver);

    @Override
    public Type replaceParam(String name, Type replaced) {
        if (replaced == null) {
            throw new IllegalArgumentException();
        }
        List<Type> newParams = typeParameters.stream().map((tp) -> tp.replaceParam(name, replaced)).collect(Collectors.toList());
        if (typeParameters.equals(newParams)) {
            return this;
        } else {
            return create(typeDeclaration, newParams, typeSolver);
        }
    }

    /**
     * Return all ancestors, that means all superclasses and interfaces.
     * This list should always include Object (unless this is a reference to Object).
     * The type typeParametersValues should be expressed in terms of this type typeParametersValues.
     *
     * For example, given:
     *
     * class Foo<A, B> {}
     * class Bar<C> extends Foo<C, String> {}
     *
     * a call to getAllAncestors on a reference to Bar having type parameter Boolean should include
     * Foo<Boolean, String>.
     */
    public List<ReferenceType> getAllAncestors() {
        List<ReferenceType> ancestors = typeDeclaration.getAllAncestors();

        TypeDeclaration objectType = typeSolver.solveType(Object.class.getCanonicalName());
        ReferenceType objectRef = create(objectType, typeSolver);

        ancestors = ancestors.stream().map((a) -> replaceTypeParams(a).asReferenceType()).collect(Collectors.toList());
        // TODO replace type typeParametersValues

        for (int i = 0; i < ancestors.size(); i++) {
            if (ancestors.get(i).getQualifiedName().equals(Object.class.getCanonicalName())) {
                ancestors.remove(i);
                i--;
            }
        }
        ancestors.add(objectRef);
        return ancestors;
    }

    public List<ReferenceType> getAllInterfacesAncestors() {
        return getAllAncestors().stream()
                .filter(it -> it.getTypeDeclaration().isInterface())
                .collect(Collectors.toList());
    }

    /**
     * Replace the type typeParametersValues present in the given type with the ones for which this type
     * has a value.
     */
    @Deprecated
    public Type replaceTypeParams(Type type) {
        if (type.isTypeVariable()) {
            TypeParameterDeclaration typeParameter = type.asTypeParameter();
            if (typeParameter.declaredOnClass()) {
                Optional<Type> typeParam = typeParamByName(typeParameter.getName());
                if (typeParam.isPresent()) {
                    type = typeParam.get();
                }
            }
        }

        if (type.isReferenceType()) {
            for (int i = 0; i < type.asReferenceType().typeParametersValues().size(); i++) {
                Type replaced = replaceTypeParams(type.asReferenceType().typeParametersValues().get(i));
                // Identity comparison on purpose
                if (replaced != type.asReferenceType().typeParametersValues().get(i)) {
                    type = type.asReferenceType().replaceParam(i, replaced);
                }
            }
        }

        return type;
    }

    @Override
    public String describe() {
        StringBuilder sb = new StringBuilder();
        if (hasName()) {
            sb.append(typeDeclaration.getQualifiedName());
        } else {
            sb.append("<anonymous class>");
        }
        if (!typeParametersValues().isEmpty()) {
            sb.append("<");
            boolean first = true;
            for (Type param : typeParametersValues()) {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }
                sb.append(param.describe());
            }
            sb.append(">");
        }
        return sb.toString();
    }

    @Deprecated
    public List<Type> typeParametersValues() {
        return typeParameters;
    }

    @Override
    public abstract TypeParameterDeclaration asTypeParameter();

    @Override
    public boolean isTypeVariable() {
        return typeDeclaration.isTypeVariable();
    }
    
    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    @Override
    public abstract boolean isAssignableBy(Type other);

    public boolean hasName() {
        return typeDeclaration.hasName();
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

    public String getQualifiedName() {
        return typeDeclaration.getQualifiedName();
    }

    public abstract Set<MethodUsage> getDeclaredMethods();
    
    public boolean isRawType() {
    	return (!typeDeclaration.getTypeParameters().isEmpty() && 
    			typeParameters.isEmpty());
    }

    @Deprecated
    public List<Tuple2<TypeParameterDeclaration, Type>> getTypeParametersMap() {
        List<Tuple2<TypeParameterDeclaration, Type>> typeParametersMap = new ArrayList<>();
        for (int i=0;i<typeDeclaration.getTypeParameters().size(); i++) {
            typeParametersMap.add(new Tuple2<>(typeDeclaration.getTypeParameters().get(0), typeParametersValues().get(i)));
        }
        return typeParametersMap;
    }

    @Override
    public TypeParametersMap typeParametersMap() {
        return typeParametersMap;
    }
}
