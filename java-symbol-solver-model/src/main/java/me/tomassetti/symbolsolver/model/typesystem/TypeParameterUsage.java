package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.model.resolution.TypeParameter;

/**
 * @author Federico Tomassetti
 */
public class TypeParameterUsage implements TypeUsage {

    private TypeParameter typeParameter;

    public TypeParameterUsage(TypeParameter typeParameter) {
        this.typeParameter = typeParameter;
    }

    @Override
    public String toString() {
        return "TypeUsageOfTypeParameter{" +
                "typeParameter=" + typeParameter +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TypeParameterUsage that = (TypeParameterUsage) o;

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
    public TypeUsage replaceParam(String name, TypeUsage replaced) {
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
    public TypeParameter asTypeParameter() {
        return typeParameter;
    }

    @Override
    public boolean isTypeVariable() {
        return true;
    }

    @Override
    public boolean isAssignableBy(TypeUsage other) {
        if (other.isTypeVariable()) {
            return describe().equals(other.describe());
        } else {
            return false;
        }
    }

}
