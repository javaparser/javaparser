package com.github.javaparser.symbolsolver.resolution.typeinference.bounds;

import com.github.javaparser.symbolsolver.resolution.typeinference.Bound;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariable;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariableSubstitution;

import java.util.HashSet;
import java.util.Set;

/**
 * The inference variable α appears in a throws clause.
 *
 * A bound of the form throws α is purely informational: it directs resolution to optimize the instantiation of α so
 * that, if possible, it is not a checked exception type.
 *
 * @author Federico Tomassetti
 */
public class ThrowsBound extends Bound {
    private InferenceVariable inferenceVariable;

    public ThrowsBound(InferenceVariable inferenceVariable) {
        this.inferenceVariable = inferenceVariable;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ThrowsBound that = (ThrowsBound) o;

        return inferenceVariable.equals(that.inferenceVariable);
    }

    @Override
    public String toString() {
        return "ThrowsBound{" +
                "inferenceVariable=" + inferenceVariable +
                '}';
    }

    @Override
    public int hashCode() {
        return inferenceVariable.hashCode();
    }

    @Override
    public Set<InferenceVariable> usedInferenceVariables() {
        Set<InferenceVariable> variables = new HashSet<>();
        variables.add(inferenceVariable);
        return variables;
    }

    @Override
    public boolean isSatisfied(InferenceVariableSubstitution inferenceVariableSubstitution) {
        throw new UnsupportedOperationException();
    }

    public boolean isThrowsBoundOn(InferenceVariable inferenceVariable) {
        return inferenceVariable.equals(this.inferenceVariable);
    }
}
