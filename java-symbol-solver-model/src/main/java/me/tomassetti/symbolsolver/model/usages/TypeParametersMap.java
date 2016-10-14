package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.model.usages.typesystem.TypeParameter;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class TypeParametersMap {
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TypeParametersMap)) return false;

        TypeParametersMap that = (TypeParametersMap) o;

        return nameToValue.equals(that.nameToValue);

    }

    @Override
    public int hashCode() {
        return nameToValue.hashCode();
    }

    @Override
    public String toString() {
        return "TypeParametersMap{" +
                "nameToValue=" + nameToValue +
                '}';
    }

    private Map<String, Type> nameToValue;

    public TypeParametersMap() {
        nameToValue = new HashMap<>();
    }

    public void setValue(TypeParameterDeclaration typeParameter, Type value) {
        String qualifiedName = typeParameter.getQualifiedName();
        nameToValue.put(qualifiedName, value);
    }

    public Type getValue(TypeParameterDeclaration typeParameter) {
        String qualifiedName = typeParameter.getQualifiedName();
        if (nameToValue.containsKey(qualifiedName)) {
            return nameToValue.get(qualifiedName);
        } else {
            return new TypeParameter(typeParameter);
        }
    }

    public Optional<Type> getValueBySignature(String signature) {
        if (nameToValue.containsKey(signature)) {
            return Optional.of(nameToValue.get(signature));
        } else {
            return Optional.empty();
        }
    }
}
