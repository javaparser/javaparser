package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.symbolsolver.model.typesystem.Type;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class InferenceVariableSubstitution {

    private final static InferenceVariableSubstitution EMPTY = new InferenceVariableSubstitution();

    private List<InferenceVariable> inferenceVariables;
    private List<Type> types;

    public static InferenceVariableSubstitution empty() {
        return EMPTY;
    }

    private InferenceVariableSubstitution() {
        this.inferenceVariables = new LinkedList<>();
        this.types = new LinkedList<>();
    }

    public InferenceVariableSubstitution withPair(InferenceVariable inferenceVariable, Type type) {
        InferenceVariableSubstitution newInstance = new InferenceVariableSubstitution();
        newInstance.inferenceVariables.addAll(this.inferenceVariables);
        newInstance.types.addAll(this.types);
        newInstance.inferenceVariables.add(inferenceVariable);
        newInstance.types.add(type);
        return newInstance;
    }

}
