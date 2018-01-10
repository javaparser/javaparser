package com.github.javaparser.symbolsolver.resolution.typeinference.bounds;

import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.Bound;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariable;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariableSubstitution;
import com.github.javaparser.symbolsolver.resolution.typeinference.Instantiation;
import com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isInferenceVariable;
import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isProperType;

/**
 * S = T, where at least one of S or T is an inference variable: S is the same as T.
 *
 * @author Federico Tomassetti
 */
public class SameAsBound extends Bound {
    private ResolvedType s;
    private ResolvedType t;

    public SameAsBound(ResolvedType s, ResolvedType t) {
        if (!isInferenceVariable(s) && !isInferenceVariable(t)) {
            throw new IllegalArgumentException("One of S or T should be an inference variable");
        }
        this.s = s;
        this.t = t;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        SameAsBound that = (SameAsBound) o;

        if (!s.equals(that.s)) return false;
        return t.equals(that.t);
    }

    @Override
    public String toString() {
        return "SameAsBound{" +
                "s=" + s +
                ", t=" + t +
                '}';
    }

    @Override
    public int hashCode() {
        int result = s.hashCode();
        result = 31 * result + t.hashCode();
        return result;
    }

    @Override
    public Set<InferenceVariable> usedInferenceVariables() {
        Set<InferenceVariable> variables = new HashSet<>();
        variables.addAll(TypeHelper.usedInferenceVariables(s));
        variables.addAll(TypeHelper.usedInferenceVariables(t));
        return variables;
    }

    public ResolvedType getS() {
        return s;
    }

    public ResolvedType getT() {
        return t;
    }

    @Override
    public boolean isADependency() {
        return !isAnInstantiation().isPresent();
    }

    @Override
    public Optional<Instantiation> isAnInstantiation() {
        if (isInferenceVariable(s) && isProperType(t)) {
            return Optional.of(new Instantiation((InferenceVariable) s, t));
        }
        if (isProperType(s) && isInferenceVariable(t)) {
            return Optional.of(new Instantiation((InferenceVariable) t, s));
        }
        return Optional.empty();
    }

    @Override
    public boolean isSatisfied(InferenceVariableSubstitution inferenceVariableSubstitution) {
        throw new UnsupportedOperationException();
    }
}
