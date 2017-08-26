package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.symbolsolver.model.typesystem.Type;

/**
 * @author Federico Tomassetti
 */
public class Instantiation {
    private InferenceVariable inferenceVariable;
    private Type properType;

    public Instantiation(InferenceVariable inferenceVariable, Type properType) {
        this.inferenceVariable = inferenceVariable;
        this.properType = properType;
    }

    public InferenceVariable getInferenceVariable() {
        return inferenceVariable;
    }

    public Type getProperType() {
        return properType;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Instantiation that = (Instantiation) o;

        if (!inferenceVariable.equals(that.inferenceVariable)) return false;
        return properType.equals(that.properType);
    }

    @Override
    public int hashCode() {
        int result = inferenceVariable.hashCode();
        result = 31 * result + properType.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "Instantiation{" +
                "inferenceVariable=" + inferenceVariable +
                ", properType=" + properType +
                '}';
    }
}
