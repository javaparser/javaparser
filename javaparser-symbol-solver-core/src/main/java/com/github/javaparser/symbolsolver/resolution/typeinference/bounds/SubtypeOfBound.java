package com.github.javaparser.symbolsolver.resolution.typeinference.bounds;

import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.*;
import com.github.javaparser.utils.Pair;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isInferenceVariable;
import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isProperType;

/**
 * S <: T, where at least one of S or T is an inference variable: S is a subtype of T
 *
 * @author Federico Tomassetti
 */
public class SubtypeOfBound extends Bound {
    private ResolvedType s;
    private ResolvedType t;

    public SubtypeOfBound(ResolvedType s, ResolvedType t) {
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

        SubtypeOfBound that = (SubtypeOfBound) o;

        if (!s.equals(that.s)) return false;
        return t.equals(that.t);
    }

    @Override
    public String toString() {
        return "SubtypeOfBound{" +
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

    public ResolvedType getS() {
        return s;
    }

    @Override
    public Set<InferenceVariable> usedInferenceVariables() {
        Set<InferenceVariable> variables = new HashSet<>();
        variables.addAll(TypeHelper.usedInferenceVariables(s));
        variables.addAll(TypeHelper.usedInferenceVariables(t));
        return variables;
    }

    public ResolvedType getT() {
        return t;
    }

    @Override
    public Optional<ProperUpperBound> isProperUpperBound() {
        if (isInferenceVariable(s) && isProperType(t)) {
            return Optional.of(new ProperUpperBound((InferenceVariable) s, t));
        }
        return Optional.empty();
    }

    @Override
    public Optional<ProperLowerBound> isProperLowerBound() {
        if (isProperType(s) && isInferenceVariable(t)) {
            return Optional.of(new ProperLowerBound((InferenceVariable) t, s));
        }
        return Optional.empty();
    }

    @Override
    public boolean isADependency() {
        return !isProperLowerBound().isPresent() && !isProperUpperBound().isPresent();
    }

    @Override
    public boolean isSatisfied(InferenceVariableSubstitution inferenceVariableSubstitution) {
        throw new UnsupportedOperationException();
    }
}
