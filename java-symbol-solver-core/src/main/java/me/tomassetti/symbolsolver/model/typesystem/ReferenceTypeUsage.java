package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.LambdaArgumentTypeUsagePlaceholder;
import me.tomassetti.symbolsolver.resolution.javaparser.declarations.JavaParserTypeVariableDeclaration;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

// TODO Remove references to typeSolver: it is needed to instantiate other instances of ReferenceTypeUsage
//      and to get the Object type declaration
public class ReferenceTypeUsage implements TypeUsage {

    private TypeDeclaration typeDeclaration;
    private List<TypeUsage> typeParameters;
    private TypeSolver typeSolver;

    public ReferenceTypeUsage(TypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        this(typeDeclaration, deriveParams(typeDeclaration), typeSolver);
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    public ReferenceTypeUsage(TypeDeclaration typeDeclaration, List<TypeUsage> typeParameters, TypeSolver typeSolver) {
        this.typeDeclaration = typeDeclaration;
        this.typeParameters = typeParameters;
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    private static List<TypeUsage> deriveParams(TypeDeclaration typeDeclaration) {
        return typeDeclaration.getTypeParameters().stream().map((tp) -> new TypeParameterUsage(tp)).collect(Collectors.toList());
    }

    public ReferenceTypeUsage asReferenceTypeUsage() {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReferenceTypeUsage that = (ReferenceTypeUsage) o;

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
                ", typeParameters=" + typeParameters +
                '}';
    }

    private Optional<TypeUsage> typeParamByName(String name) {
        List<TypeUsage> typeParameters = this.typeParameters;
        TypeDeclaration objectType = typeSolver.solveType(Object.class.getCanonicalName());
        ReferenceTypeUsage objectRef = new ReferenceTypeUsage(objectType, typeSolver);
        if (typeDeclaration.getTypeParameters().size() != typeParameters.size()) {
            if (typeParameters.size() > 0) {
                throw new UnsupportedOperationException();
            }
            // type parameters not specified, default to Object
            typeParameters = new ArrayList<>();
            for (int i = 0; i < typeDeclaration.getTypeParameters().size(); i++) {
                typeParameters.add(objectRef);
            }
        }
        int i = 0;
        for (TypeParameter tp : typeDeclaration.getTypeParameters()) {
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
    public Optional<TypeUsage> getFieldType(String name) {
        if (!typeDeclaration.hasField(name)) {
            return Optional.empty();
        }
        TypeUsage typeUsage = typeDeclaration.getField(name).getType();
        typeUsage = replaceTypeParams(typeUsage);
        return Optional.of(typeUsage);
    }

    /**
     * Get the type associated with the type parameter with the given name.
     * It returns Optional.empty unless the type declaration declares a type parameter with the given name.
     */
    public Optional<TypeUsage> getGenericParameterByName(String name) {
        int i = 0;
        for (TypeParameter tp : typeDeclaration.getTypeParameters()) {
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
    public TypeUsage replaceParam(int i, TypeUsage replaced) {
        ArrayList<TypeUsage> typeParametersCorrected = new ArrayList<>(typeParameters);
        typeParametersCorrected.set(i, replaced);
        return new ReferenceTypeUsage(typeDeclaration, typeParametersCorrected, typeSolver);
    }

    @Override
    public TypeUsage replaceParam(String name, TypeUsage replaced) {
        List<TypeUsage> newParams = typeParameters.stream().map((tp) -> tp.replaceParam(name, replaced)).collect(Collectors.toList());
        if (typeParameters.equals(newParams)) {
            return this;
        } else {
            return new ReferenceTypeUsage(typeDeclaration, newParams, typeSolver);
        }
    }

    /**
     * Return all ancestors, that means all superclasses and interfaces.
     * This list should always include Object (unless this is a reference to Object).
     * The type parameters should be expressed in terms of this type parameters.
     *
     * For example, given:
     *
     * class Foo<A, B> {}
     * class Bar<C> extends Foo<C, String> {}
     *
     * a call to getAllAncestors on a reference to Bar having type parameter Boolean should include
     * Foo<Boolean, String>.
     */
    public List<ReferenceTypeUsage> getAllAncestors() {
        List<ReferenceTypeUsage> ancestors = typeDeclaration.getAllAncestors();

        TypeDeclaration objectType = typeSolver.solveType(Object.class.getCanonicalName());
        ReferenceTypeUsage objectRef = new ReferenceTypeUsage(objectType, typeSolver);

        ancestors = ancestors.stream().map((a) -> replaceTypeParams(a).asReferenceTypeUsage()).collect(Collectors.toList());
        // TODO replace type parameters

        for (int i = 0; i < ancestors.size(); i++) {
            if (ancestors.get(i).getQualifiedName().equals(Object.class.getCanonicalName())) {
                ancestors.remove(i);
                i--;
            }
        }
        ancestors.add(objectRef);
        return ancestors;
    }

    public TypeUsage replaceTypeParams(TypeUsage typeUsage) {
        if (typeUsage.isTypeVariable()) {
            TypeParameter typeParameter = typeUsage.asTypeParameter();
            if (typeParameter.declaredOnClass()) {
                Optional<TypeUsage> typeParam = typeParamByName(typeParameter.getName());
                if (typeParam.isPresent()) {
                    typeUsage = typeParam.get();
                }
            }
        }

        if (typeUsage.isReferenceType()) {
            for (int i = 0; i < typeUsage.asReferenceTypeUsage().parameters().size(); i++) {
                TypeUsage replaced = replaceTypeParams(typeUsage.asReferenceTypeUsage().parameters().get(i));
                // Identity comparison on purpose
                if (replaced != typeUsage.asReferenceTypeUsage().parameters().get(i)) {
                    typeUsage = typeUsage.asReferenceTypeUsage().replaceParam(i, replaced);
                }
            }
        }

        return typeUsage;
    }

    @Override
    public String describe() {
        StringBuffer sb = new StringBuffer();
        if (hasName()) {
            sb.append(typeDeclaration.getQualifiedName());
        } else {
            sb.append("<anonymous class>");
        }
        if (parameters().size() > 0) {
            sb.append("<");
            boolean first = true;
            for (TypeUsage param : parameters()) {
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

    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
        return typeDeclaration.solveMethod(name, parameterTypes);
    }

    public List<TypeUsage> parameters() {
        return typeParameters;
    }

    @Override
    public TypeParameter asTypeParameter() {
        if (this.typeDeclaration instanceof JavaParserTypeVariableDeclaration) {
            JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration) this.typeDeclaration;
            return javaParserTypeVariableDeclaration.asTypeParameter();
        }
        throw new UnsupportedOperationException(this.typeDeclaration.getClass().getCanonicalName());
    }

    @Override
    public boolean isTypeVariable() {
        return typeDeclaration.isTypeVariable();
    }

    @Override
    public boolean isAssignableBy(TypeUsage other) {
        if (other instanceof NullTypeUsage) {
            return !this.isPrimitive();
        }
        // consider boxing
        if (other.isPrimitive()) {
            if (this.getQualifiedName().equals(Object.class.getCanonicalName())) {
                return true;
            } else {
                return isCorrespondingBoxingType(other.describe());
            }
        }
        if (other instanceof LambdaArgumentTypeUsagePlaceholder) {
            return this.getQualifiedName().equals(Predicate.class.getCanonicalName()) || this.getQualifiedName().equals(Function.class.getCanonicalName());
        } else if (other instanceof ReferenceTypeUsage) {
            ReferenceTypeUsage otherRef = (ReferenceTypeUsage) other;
            if (compareConsideringTypeParameters(otherRef)) {
                return true;
            }
            for (ReferenceTypeUsage otherAncestor : otherRef.getAllAncestors()) {
                if (compareConsideringTypeParameters(otherAncestor)) {
                    return true;
                }
            }
            return false;
        } else if (other.isTypeVariable()) {
            // TODO look bounds...
            return true;
        } else {
            return false;
        }
    }

    public boolean hasName() {
        return typeDeclaration.hasName();
    }

    private boolean compareConsideringTypeParameters(ReferenceTypeUsage other) {
        if (other.equals(this)) {
            return true;
        }
        if (this.getQualifiedName().equals(other.getQualifiedName())) {
            if (this.parameters().size() != other.parameters().size()) {
                throw new IllegalStateException();
            }
            for (int i = 0; i < parameters().size(); i++) {
                TypeUsage thisParam = parameters().get(i);
                TypeUsage otherParam = other.parameters().get(i);
                if (!thisParam.equals(otherParam)) {
                    if (thisParam instanceof WildcardUsage) {
                        WildcardUsage thisParamAsWildcard = (WildcardUsage) thisParam;
                        if (thisParamAsWildcard.isSuper() && thisParamAsWildcard.getBoundedType().equals(otherParam)) {
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

    private boolean isCorrespondingBoxingType(String typeName) {
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

}
