package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.model.usages.typesystem.TypeParameter;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Federico Tomassetti
 */
public class TypeParametersMap {

    private Map<String, Type> nameToValue;

    public TypeParametersMap() {
        nameToValue = new HashMap<>();
    }

    public void setValue(TypeParameterDeclaration typeParameter, Type value) {
        String qualifiedName = typeParameter.qualifiedName();
        nameToValue.put(qualifiedName, value);
    }

    public Type getValue(TypeParameterDeclaration typeParameter) {
        String qualifiedName = typeParameter.qualifiedName();
        if (nameToValue.containsKey(qualifiedName)) {
            return nameToValue.get(qualifiedName);
        } else {
            return new TypeParameter(typeParameter);
        }
    }

}
