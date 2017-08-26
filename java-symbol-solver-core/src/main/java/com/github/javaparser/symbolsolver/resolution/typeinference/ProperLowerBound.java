package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.symbolsolver.model.typesystem.Type;

/**
 * @author Federico Tomassetti
 */
public class ProperLowerBound {
    private InferenceVariable inferenceVariable;
    private Type properType;

    public ProperLowerBound(InferenceVariable inferenceVariable, Type properType) {
        this.inferenceVariable = inferenceVariable;
        this.properType = properType;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProperLowerBound that = (ProperLowerBound) o;

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
        return "ProperLowerBound{" +
                "inferenceVariable=" + inferenceVariable +
                ", properType=" + properType +
                '}';
    }

    public InferenceVariable getInferenceVariable() {
        return inferenceVariable;
    }

    public Type getProperType() {
        return properType;
    }
}
