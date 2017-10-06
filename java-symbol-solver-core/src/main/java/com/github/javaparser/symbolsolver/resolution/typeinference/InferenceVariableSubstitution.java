package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.resolution.types.ResolvedType;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class InferenceVariableSubstitution {

    private final static InferenceVariableSubstitution EMPTY = new InferenceVariableSubstitution();

    private List<InferenceVariable> inferenceVariables;
    private List<ResolvedType> types;

    public static InferenceVariableSubstitution empty() {
        return EMPTY;
    }

    private InferenceVariableSubstitution() {
        this.inferenceVariables = new LinkedList<>();
        this.types = new LinkedList<>();
    }

    public InferenceVariableSubstitution withPair(InferenceVariable inferenceVariable, ResolvedType type) {
        InferenceVariableSubstitution newInstance = new InferenceVariableSubstitution();
        newInstance.inferenceVariables.addAll(this.inferenceVariables);
        newInstance.types.addAll(this.types);
        newInstance.inferenceVariables.add(inferenceVariable);
        newInstance.types.add(type);
        return newInstance;
    }

}
