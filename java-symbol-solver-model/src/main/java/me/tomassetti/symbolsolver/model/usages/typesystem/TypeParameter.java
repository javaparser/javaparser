package me.tomassetti.symbolsolver.model.usages.typesystem;

import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;

/**
 * @author Federico Tomassetti
 */
public class TypeParameter implements Type {

    private TypeParameterDeclaration typeParameter;

    public TypeParameter(TypeParameterDeclaration typeParameter) {
        this.typeParameter = typeParameter;
    }

    @Override
    public String toString() {
        return "TypeUsageOfTypeParameter{" + typeParameter + "}";
    }

    public String qualifiedName() {
        return this.typeParameter.getQualifiedName();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TypeParameter that = (TypeParameter) o;

        if (!typeParameter.getName().equals(that.typeParameter.getName())) return false;
        if (typeParameter.declaredOnClass() != that.typeParameter.declaredOnClass()) return false;
        if (typeParameter.declaredOnMethod() != that.typeParameter.declaredOnMethod()) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return typeParameter.hashCode();
    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return false;
    }

    @Override
    public Type replaceParam(String name, Type replaced) {
        if (name.equals(typeParameter.getName())) {
            return replaced;
        } else {
            return this;
        }
    }

    @Override
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String describe() {
        return typeParameter.getName();
    }

    @Override
    public TypeParameterDeclaration asTypeParameter() {
        return typeParameter;
    }

    @Override
    public boolean isTypeVariable() {
        return true;
    }

    @Override
    public boolean isAssignableBy(Type other) {
        if (other.isTypeVariable()) {
            return describe().equals(other.describe());
        } else {
            return false;
        }
    }

}
