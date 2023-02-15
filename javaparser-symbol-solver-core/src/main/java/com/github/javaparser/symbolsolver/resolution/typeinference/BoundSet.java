/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.CapturesBound;
import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.FalseBound;
import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.SameAsBound;
import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.SubtypeOfBound;
import com.github.javaparser.symbolsolver.resolution.typeinference.constraintformulas.TypeSameAsType;
import com.github.javaparser.symbolsolver.resolution.typeinference.constraintformulas.TypeSubtypeOfType;
import com.github.javaparser.utils.Pair;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.*;

/**
 * @author Federico Tomassetti
 */
public class BoundSet {
    
    private static String JAVA_LANG_RUNTIME_EXCEPTION = RuntimeException.class.getCanonicalName();
    
    private static final BoundSet EMPTY = new BoundSet();

    private List<Bound> bounds = new LinkedList<>();

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        BoundSet boundSet = (BoundSet) o;

        return new HashSet<>(bounds).equals(new HashSet<>(boundSet.bounds));
    }

    @Override
    public int hashCode() {
        return bounds.hashCode();
    }

    @Override
    public String toString() {
        return "BoundSet{" +
                "bounds=" + bounds +
                '}';
    }

    /**

     * It is sometimes convenient to refer to an empty bound set with the symbol true; this is merely out of
     * convenience, and the two are interchangeable.
     */
    public boolean isTrue() {
        return bounds.isEmpty();
    }

    public static BoundSet empty() {
        return EMPTY;
    }

    public BoundSet withBound(Bound bound) {
        if (this.bounds.contains(bound)) {
            return this;
        }
        BoundSet boundSet = new BoundSet();
        boundSet.bounds.addAll(this.bounds);
        boundSet.bounds.add(bound);
        return boundSet;
    }

    private Optional<Pair<SameAsBound, SameAsBound>> findPairSameAs(Predicate<Pair<SameAsBound, SameAsBound>> condition) {
        for (int i=0;i<bounds.size();i++) {
            Bound bi = bounds.get(i);
            if (bi instanceof SameAsBound) {
                SameAsBound si = (SameAsBound)bi;
                for (int j = i + 1; j < bounds.size(); j++) {
                    Bound bj = bounds.get(j);
                    if (bj instanceof SameAsBound) {
                        SameAsBound sj = (SameAsBound)bj;
                        Pair<SameAsBound, SameAsBound> pair = new Pair<SameAsBound, SameAsBound>(si, sj);
                        if (condition.test(pair)) {
                            return Optional.of(pair);
                        }
                    }
                }
            }
        }
        return Optional.empty();
    }

    public boolean isEmpty() {
        return bounds.isEmpty();
    }

    interface Processor<B1 extends Bound, B2 extends Bound, R> {
        R process(B1 a, B2 b, R initialValue);
    }

    private <T> T forEachPairSameAs(Processor<SameAsBound, SameAsBound, T> processor, T initialValue) {
        T currentValue = initialValue;
        for (int i=0;i<bounds.size();i++) {
            Bound bi = bounds.get(i);
            if (bi instanceof SameAsBound) {
                SameAsBound si = (SameAsBound)bi;
                for (int j = i + 1; j < bounds.size(); j++) {
                    Bound bj = bounds.get(j);
                    if (bj instanceof SameAsBound) {
                        SameAsBound sj = (SameAsBound)bj;
                        currentValue = processor.process(si, sj, currentValue);
                    }
                }
            }
        }
        return currentValue;
    }

    private <T> T forEachPairSameAndSubtype(Processor<SameAsBound, SubtypeOfBound, T> processor, T initialValue) {
        T currentValue = initialValue;
        for (int i=0;i<bounds.size();i++) {
            Bound bi = bounds.get(i);
            if (bi instanceof SameAsBound) {
                SameAsBound si = (SameAsBound)bi;
                for (int j = i + 1; j < bounds.size(); j++) {
                    Bound bj = bounds.get(j);
                    if (bj instanceof SubtypeOfBound) {
                        SubtypeOfBound sj = (SubtypeOfBound)bj;
                        currentValue = processor.process(si, sj, currentValue);
                    }
                }
            }
        }
        return currentValue;
    }

    private <T> T forEachPairSubtypeAndSubtype(Processor<SubtypeOfBound, SubtypeOfBound, T> processor, T initialValue) {
        T currentValue = initialValue;
        for (int i=0;i<bounds.size();i++) {
            Bound bi = bounds.get(i);
            if (bi instanceof SubtypeOfBound) {
                SubtypeOfBound si = (SubtypeOfBound)bi;
                for (int j = i + 1; j < bounds.size(); j++) {
                    Bound bj = bounds.get(j);
                    if (bj instanceof SubtypeOfBound) {
                        SubtypeOfBound sj = (SubtypeOfBound)bj;
                        currentValue = processor.process(si, sj, currentValue);
                    }
                }
            }
        }
        return currentValue;
    }

    private boolean areSameTypeInference(ResolvedType a, ResolvedType b) {
        return a.isInferenceVariable() && b.isInferenceVariable() && a.equals(b);
    }

    private List<Pair<ResolvedReferenceType, ResolvedReferenceType>> findPairsOfCommonAncestors(ResolvedReferenceType r1, ResolvedReferenceType r2) {
        List<ResolvedReferenceType> set1 = new LinkedList<>();
        set1.add(r1);
        set1.addAll(r1.getAllAncestors());
        List<ResolvedReferenceType> set2 = new LinkedList<>();
        set2.add(r2);
        set2.addAll(r2.getAllAncestors());
        List<Pair<ResolvedReferenceType, ResolvedReferenceType>> pairs = new LinkedList<>();
        for (ResolvedReferenceType rtFrom1 : set1) {
            for (ResolvedReferenceType rtFrom2 : set2) {
                Optional<ResolvedReferenceTypeDeclaration> rtFrom1TypeDeclaration = rtFrom1.getTypeDeclaration();
                Optional<ResolvedReferenceTypeDeclaration> rtFrom2TypeDeclaration = rtFrom2.getTypeDeclaration();
                if (rtFrom1TypeDeclaration.isPresent() && rtFrom2TypeDeclaration.isPresent()) {
                    if(rtFrom1TypeDeclaration.get().equals(rtFrom2TypeDeclaration.get())) {
                        pairs.add(new Pair<>(rtFrom1, rtFrom2));
                    }
                }
            }
        }
        return pairs;
    }

    /**
     * Maintains a set of inference variable bounds, ensuring that these are consistent as new bounds are added.
     * Because the bounds on one variable can sometimes impact the possible choices for another variable, this process
     * propagates bounds between such interdependent variables.
     */
    public BoundSet incorporate(BoundSet otherBounds, TypeSolver typeSolver) {
        BoundSet newBoundSet = this;
        for (Bound b : otherBounds.bounds) {
            newBoundSet = newBoundSet.withBound(b);
        }
        return newBoundSet.deriveImpliedBounds(typeSolver);
    }

    public BoundSet deriveImpliedBounds(TypeSolver typeSolver) {
        // As bound sets are constructed and grown during inference, it is possible that new bounds can be inferred
        // based on the assertions of the original bounds. The process of incorporation identifies these new bounds
        // and adds them to the bound set.
        //
        // Incorporation can happen in two scenarios. One scenario is that the bound set contains complementary pairs
        // of bounds; this implies new constraint formulas, as specified in §18.3.1. The other scenario is that the
        // bound set contains a bound involving capture conversion; this implies new bounds and may imply new
        // constraint formulas, as specified in §18.3.2. In both scenarios, any new constraint formulas are reduced,
        // and any new bounds are added to the bound set. This may trigger further incorporation; ultimately, the set
        // will reach a fixed point and no further bounds can be inferred.
        //
        // If incorporation of a bound set has reached a fixed point, and the set does not contain the bound false,
        // then the bound set has the following properties:
        //
        // - For each combination of a proper lower bound L and a proper upper bound U of an inference variable, L <: U.
        //
        // - If every inference variable mentioned by a bound has an instantiation, the bound is satisfied by the
        //   corresponding substitution.
        //
        // - Given a dependency α = β, every bound of α matches a bound of β, and vice versa.
        //
        // - Given a dependency α <: β, every lower bound of α is a lower bound of β, and every upper bound of β is an
        //   upper bound of α.

        ConstraintFormulaSet newConstraintsSet = ConstraintFormulaSet.empty();

        // SECTION Complementary Pairs of Bounds
        // (In this section, S and T are inference variables or types, and U is a proper type. For conciseness, a bound
        // of the form α = T may also match a bound of the form T = α.)
        //
        // When a bound set contains a pair of bounds that match one of the following rules, a new constraint formula
        // is implied:
        //
        // - α = S and α = T imply ‹S = T›

        newConstraintsSet = forEachPairSameAs((a, b, currentConstraintSet) -> {
            if (areSameTypeInference(a.getS(), b.getS())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(a.getT(), b.getT()));
            }
            if (areSameTypeInference(a.getS(), b.getT())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(a.getS(), b.getT()));
            }
            if (areSameTypeInference(a.getT(), b.getS())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(a.getT(), b.getS()));
            }
            if (areSameTypeInference(a.getT(), b.getT())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(a.getS(), b.getS()));
            }
            return currentConstraintSet;
        }, newConstraintsSet);

        // - α = S and α <: T imply ‹S <: T›

        newConstraintsSet = forEachPairSameAndSubtype((a, b, currentConstraintSet) -> {
            if (areSameTypeInference(a.getS(), b.getS())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSubtypeOfType(typeSolver, a.getT(), b.getT()));
            }
            if (areSameTypeInference(a.getT(), b.getS())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSubtypeOfType(typeSolver, a.getS(), b.getT()));
            }
            return currentConstraintSet;
        }, newConstraintsSet);

        // - α = S and T <: α imply ‹T <: S›

        newConstraintsSet = forEachPairSameAndSubtype((a, b, currentConstraintSet) -> {
            if (areSameTypeInference(a.getS(), b.getT())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSubtypeOfType(typeSolver, b.getS(), a.getT()));
            }
            if (areSameTypeInference(a.getT(), b.getT())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSubtypeOfType(typeSolver, b.getS(), a.getS()));
            }
            return currentConstraintSet;
        }, newConstraintsSet);

        // - S <: α and α <: T imply ‹S <: T›

        newConstraintsSet = forEachPairSubtypeAndSubtype((a, b, currentConstraintSet) -> {
            if (areSameTypeInference(a.getT(), b.getS())) {
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSubtypeOfType(typeSolver, b.getS(), a.getT()));
            }
            return currentConstraintSet;
        }, newConstraintsSet);

        // - α = U and S = T imply ‹S[α:=U] = T[α:=U]›

        newConstraintsSet = forEachPairSameAs((a, b, currentConstraintSet) -> {
            if (a.getS().isInferenceVariable() && isProperType(a.getT())) {
                InferenceVariable alpha = (InferenceVariable)a.getS();
                ResolvedType U = a.getT();
                ResolvedType S = b.getS();
                ResolvedType T = b.getT();
                Substitution sub = Substitution.empty().withPair(alpha.getTypeParameterDeclaration(), U);
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(sub.apply(S), sub.apply(T)));
            }
            if (a.getT().isInferenceVariable() && isProperType(a.getS())) {
                InferenceVariable alpha = (InferenceVariable)a.getT();
                ResolvedType U = a.getS();
                ResolvedType S = b.getS();
                ResolvedType T = b.getT();
                Substitution sub = Substitution.empty().withPair(alpha.getTypeParameterDeclaration(), U);
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(sub.apply(S), sub.apply(T)));
            }
            if (b.getS().isInferenceVariable() && isProperType(b.getT())) {
                InferenceVariable alpha = (InferenceVariable)b.getS();
                ResolvedType U = b.getT();
                ResolvedType S = a.getS();
                ResolvedType T = a.getT();
                Substitution sub = Substitution.empty().withPair(alpha.getTypeParameterDeclaration(), U);
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(sub.apply(S), sub.apply(T)));
            }
            if (b.getT().isInferenceVariable() && isProperType(b.getS())) {
                InferenceVariable alpha = (InferenceVariable)b.getT();
                ResolvedType U = b.getS();
                ResolvedType S = a.getS();
                ResolvedType T = a.getT();
                Substitution sub = Substitution.empty().withPair(alpha.getTypeParameterDeclaration(), U);
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(sub.apply(S), sub.apply(T)));
            }
            return currentConstraintSet;
        }, newConstraintsSet);

        // - α = U and S <: T imply ‹S[α:=U] <: T[α:=U]›

        newConstraintsSet = forEachPairSameAndSubtype((a, b, currentConstraintSet) -> {
            if (a.getS().isInferenceVariable() && isProperType(a.getT())) {
                InferenceVariable alpha = (InferenceVariable)a.getS();
                ResolvedType U = a.getT();
                ResolvedType S = b.getS();
                ResolvedType T = b.getT();
                Substitution sub = Substitution.empty().withPair(alpha.getTypeParameterDeclaration(), U);
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSubtypeOfType(typeSolver, sub.apply(S), sub.apply(T)));
            }
            if (a.getT().isInferenceVariable() && isProperType(a.getS())) {
                InferenceVariable alpha = (InferenceVariable)a.getT();
                ResolvedType U = a.getS();
                ResolvedType S = b.getS();
                ResolvedType T = b.getT();
                Substitution sub = Substitution.empty().withPair(alpha.getTypeParameterDeclaration(), U);
                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSubtypeOfType(typeSolver, sub.apply(S), sub.apply(T)));
            }
            return currentConstraintSet;
        }, newConstraintsSet);

        // When a bound set contains a pair of bounds α <: S and α <: T, and there exists a supertype of S of the
        // form G<S1, ..., Sn> and a supertype of T of the form G<T1, ..., Tn> (for some generic class or interface, G),
        // then for all i (1 ≤ i ≤ n), if Si and Ti are types (not wildcards), the constraint formula ‹Si = Ti› is
        // implied.

        newConstraintsSet = forEachPairSubtypeAndSubtype((a, b, currentConstraintSet) -> {
            if (a.getS().isInferenceVariable() && b.getS().isInferenceVariable()) {
                if (a.getT().isReferenceType() && b.getT().isReferenceType()) {
                    ResolvedReferenceType S = a.getT().asReferenceType();
                    ResolvedReferenceType T = b.getT().asReferenceType();
                    List<Pair<ResolvedReferenceType, ResolvedReferenceType>> pairs = findPairsOfCommonAncestors(S, T);
                    for (Pair<ResolvedReferenceType, ResolvedReferenceType> pair : pairs) {
                        for (int i=0;i<Math.min(pair.a.typeParametersValues().size(), pair.b.typeParametersValues().size()); i++) {
                            ResolvedType si = pair.a.typeParametersValues().get(i);
                            ResolvedType ti = pair.b.typeParametersValues().get(i);
                            if (!si.isWildcard() && !ti.isWildcard()) {
                                currentConstraintSet = currentConstraintSet.withConstraint(new TypeSameAsType(si, ti));
                            }
                        }
                    }
                }
            }
            return currentConstraintSet;
        }, newConstraintsSet);

        // SECTION Bounds Involving Capture Conversion
        //
        // When a bound set contains a bound of the form G<α1, ..., αn> = capture(G<A1, ..., An>), new bounds are
        // implied and new constraint formulas may be implied, as follows.

        for (Bound b : this.bounds.stream().filter(b -> b instanceof CapturesBound).collect(Collectors.toList())) {
            CapturesBound capturesBound = (CapturesBound)b;

            throw new UnsupportedOperationException();

            // Let P1, ..., Pn represent the type parameters of G and let B1, ..., Bn represent the bounds of these type
            // parameters. Let θ represent the substitution [P1:=α1, ..., Pn:=αn]. Let R be a type that is not an inference
            // variable (but is not necessarily a proper type).
            //
            // A set of bounds on α1, ..., αn is implied, constructed from the declared bounds of P1, ..., Pn as specified
            // in §18.1.3.
            //
            // In addition, for all i (1 ≤ i ≤ n):
            //
            // - If Ai is not a wildcard, then the bound αi = Ai is implied.
            //
            // - If Ai is a wildcard of the form ?:
            //
            //   - αi = R implies the bound false
            //
            //   - αi <: R implies the constraint formula ‹Bi θ <: R›
            //
            //   - R <: αi implies the bound false
            //
            // - If Ai is a wildcard of the form ? extends T:
            //
            //   - αi = R implies the bound false
            //
            //   - If Bi is Object, then αi <: R implies the constraint formula ‹T <: R›
            //
            //   - If T is Object, then αi <: R implies the constraint formula ‹Bi θ <: R›
            //
            //   - R <: αi implies the bound false
            //
            // - If Ai is a wildcard of the form ? super T:
            //
            //   - αi = R implies the bound false
            //
            //   - αi <: R implies the constraint formula ‹Bi θ <: R›
            //
            //   - R <: αi implies the constraint formula ‹R <: T›
        }

        if (newConstraintsSet.isEmpty()) {
            return this;
        } else {
            BoundSet newBounds = newConstraintsSet.reduce(typeSolver);
            if (newBounds.isEmpty()) {
                return this;
            }
            return this.incorporate(newBounds, typeSolver);
        }
    }

    public boolean containsFalse() {
        return bounds.stream().anyMatch(it -> it instanceof FalseBound);
    }

    private class VariableDependency {
        private InferenceVariable depending;
        private InferenceVariable dependedOn;

        public VariableDependency(InferenceVariable depending, InferenceVariable dependedOn) {
            this.depending = depending;
            this.dependedOn = dependedOn;
        }

        public InferenceVariable getDepending() {
            return depending;
        }

        public InferenceVariable getDependedOn() {
            return dependedOn;
        }

        public boolean isReflexive() {
            return dependedOn.equals(depending);
        }
    }

    private Set<InferenceVariable> allInferenceVariables() {
        Set<InferenceVariable> variables = new HashSet<>();
        for (Bound b : bounds) {
            variables.addAll(b.usedInferenceVariables());
        }
        return variables;
    }

    private boolean hasInstantiationFor(InferenceVariable v) {
        for (Bound b : bounds) {
            if (b.isAnInstantiationFor(v)) {
                return true;
            }
        }
        return false;
    }

    private Instantiation getInstantiationFor(InferenceVariable v) {
        for (Bound b : bounds) {
            if (b.isAnInstantiationFor(v)) {
                return b.isAnInstantiation().get();
            }
        }
        throw new IllegalArgumentException();
    }

    private boolean thereIsSomeJSuchThatβequalAlphaJ(Set<InferenceVariable> alphas, InferenceVariable beta) {
        for (InferenceVariable alphaJ : alphas) {
            for (Bound b : bounds) {
                if (b instanceof SameAsBound) {
                    SameAsBound sameAsBound = (SameAsBound)b;
                    if (sameAsBound.getS().equals(alphaJ) && sameAsBound.getT().equals(beta)) {
                        return true;
                    }
                    if (sameAsBound.getT().equals(alphaJ) && sameAsBound.getS().equals(beta)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private <T> List<Set<T>> buildAllSubsetsOfSize(Set<T> allElements, int desiredSize) {
        if (desiredSize == allElements.size()) {
            return Arrays.asList(allElements);
        } else {
            List<Set<T>> res = new LinkedList<>();
            for (T element : allElements) {
                Set<T> subset = allButOne(allElements, element);
                res.addAll(buildAllSubsetsOfSize(subset, desiredSize));
            }
            return res;
        }
    }

    private <T> Set<T> allButOne(Set<T> elements, T element) {
        Set<T> set = new HashSet<T>(elements);
        set.remove(element);
        return set;
    }

    /**
     * there exists no non-empty proper subset of { α1, ..., αn } with this property.
     */
    private Optional<Set<InferenceVariable>> smallestSetWithProperty(Set<InferenceVariable> uninstantiatedVariables,
                                                                     List<VariableDependency> dependencies) {
        for (int i=1;i<=uninstantiatedVariables.size();i++) {
            for (Set<InferenceVariable> aSubSet : buildAllSubsetsOfSize(uninstantiatedVariables, i)){
                if (hasProperty(aSubSet, dependencies)) {
                    return Optional.of(aSubSet);
                }
            }
        }
        return Optional.empty();
    }

    /**
     * if αi depends on the resolution of a variable β, then either β has an instantiation
     * or there is some j such that β = αj
     * @return
     */
    private boolean hasProperty(Set<InferenceVariable> alphas, List<VariableDependency> dependencies) {
        for (InferenceVariable alphaI: alphas) {
            for (InferenceVariable beta: dependencies.stream()
                    .filter(d -> d.depending.equals(alphaI))
                    .filter(d -> !d.isReflexive())
                    .map(d -> d.dependedOn)
                    .collect(Collectors.toList())) {
                if (!hasInstantiationFor(beta) && !thereIsSomeJSuchThatβequalAlphaJ(alphas, beta)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Examines the bounds on an inference variable and determines an instantiation that is compatible with those
     * bounds. It also decides the order in which interdependent inference variables are to be resolved.
     */
    public Optional<InstantiationSet> performResolution(List<InferenceVariable> variablesToResolve, TypeSolver typeSolver) {

        if (this.containsFalse()) {
            return Optional.empty();
        }

        List<VariableDependency> dependencies = new LinkedList<>();

        // Given a bound set that does not contain the bound false, a subset of the inference variables mentioned by
        // the bound set may be resolved. This means that a satisfactory instantiation may be added to the set for each
        // inference variable, until all the requested variables have instantiations.
        //
        // Dependencies in the bound set may require that the variables be resolved in a particular order, or that
        // additional variables be resolved. Dependencies are specified as follows:
        //
        // - Given a bound of one of the following forms, where T is either an inference variable β or a type that
        // mentions β:
        //
        //   - α = T
        //
        //   - α <: T
        //
        //   - T = α
        //
        //   - T <: α
        //
        //   If α appears on the left-hand side of another bound of the form G<..., α, ...> = capture(G<...>), then β
        //   depends on the resolution of α. Otherwise, α depends on the resolution of β.

        for (Bound b : bounds) {
            if (b instanceof CapturesBound) {
                throw new UnsupportedOperationException();
            }
        }

        // - An inference variable α appearing on the left-hand side of a bound of the form
        //   G<..., α, ...> = capture(G<...>) depends on the resolution of every other inference variable mentioned in
        //   this bound (on both sides of the = sign).

        for (Bound b : bounds) {
            if (b instanceof CapturesBound) {
                throw new UnsupportedOperationException();
            }
        }

        // - An inference variable α depends on the resolution of an inference variable β if there exists an inference
        //   variable γ such that α depends on the resolution of γ and γ depends on the resolution of β.

        for (int i=0;i<dependencies.size();i++) {
            VariableDependency di = dependencies.get(i);
            for (int j=i+1;j<dependencies.size();j++) {
                VariableDependency dj = dependencies.get(j);
                if (di.dependedOn.equals(dj.depending)) {
                    dependencies.add(new VariableDependency(di.getDepending(), dj.getDependedOn()));
                }
            }
        }

        // - An inference variable α depends on the resolution of itself.

        for (InferenceVariable v : allInferenceVariables()) {
            dependencies.add(new VariableDependency(v, v));
        }

        // Given a set of inference variables to resolve, let V be the union of this set and all variables upon which
        // the resolution of at least one variable in this set depends.

        Set<InferenceVariable> V = new HashSet<>();
        V.addAll(variablesToResolve);
        for (VariableDependency dependency : dependencies) {
            if (variablesToResolve.contains(dependency.depending)) {
                V.add(dependency.dependedOn);
            }
        }

        // If every variable in V has an instantiation, then resolution succeeds and this procedure terminates.

        boolean ok = true;
        for (InferenceVariable v : V) {
            if (!hasInstantiationFor(v)) {
                ok = false;
            }
        }
        if (ok) {
            InstantiationSet instantiationSet = InstantiationSet.empty();
            for (InferenceVariable v : V) {
                instantiationSet = instantiationSet.withInstantiation(getInstantiationFor(v));
            }
            return Optional.of(instantiationSet);
        }

        // Otherwise, let { α1, ..., αn } be a non-empty subset of uninstantiated variables in V such that i)
        // for all i (1 ≤ i ≤ n), if αi depends on the resolution of a variable β, then either β has an instantiation
        // or there is some j such that β = αj; and ii) there exists no non-empty proper subset of { α1, ..., αn }
        // with this property.

        Set<InferenceVariable> uninstantiatedPortionOfV = new HashSet<>();
        for (InferenceVariable v : V) {
            if (!hasInstantiationFor(v)) {
                uninstantiatedPortionOfV.add(v);
            }
        }
        for (Set<InferenceVariable> alphas: allSetsWithProperty(uninstantiatedPortionOfV, dependencies)) {

            // Resolution proceeds by generating an instantiation for each of α1, ..., αn based on the
            // bounds in the bound set:

            boolean hasSomeCaptureForAlphas = alphas.stream().anyMatch(
                    alphaI -> appearInLeftPartOfCapture(alphaI)
            );

            // - If the bound set does not contain a bound of the form G<..., αi, ...> = capture(G<...>)
            //   for all i (1 ≤ i ≤ n), then a candidate instantiation Ti is defined for each αi:

            if (!hasSomeCaptureForAlphas) {
                BoundSet newBounds = BoundSet.empty();
                for (InferenceVariable alphaI : alphas) {
                    Set<ResolvedType> properLowerBounds = bounds.stream()
                            .filter(b -> b.isProperLowerBoundFor(alphaI).isPresent())
                            .map(b -> b.isProperLowerBoundFor(alphaI).get().getProperType())
                            .collect(Collectors.toSet());

                    ResolvedType Ti = null;

                    //   - If αi has one or more proper lower bounds, L1, ..., Lk, then Ti = lub(L1, ..., Lk) (§4.10.4).

                    if (properLowerBounds.size() > 0) {
                        Ti = leastUpperBound(properLowerBounds);
                    }

                    //   - Otherwise, if the bound set contains throws αi, and the proper upper bounds of αi are, at most,
                    //     Exception, Throwable, and Object, then Ti = RuntimeException.

                    boolean throwsBound = bounds.stream().anyMatch(b -> b.isThrowsBoundOn(alphaI));
                    if (Ti == null && throwsBound && properUpperBoundsAreAtMostExceptionThrowableAndObject(alphaI)) {
                        Ti = new ReferenceTypeImpl(typeSolver.solveType(JAVA_LANG_RUNTIME_EXCEPTION));
                    }

                    //   - Otherwise, where αi has proper upper bounds U1, ..., Uk, Ti = glb(U1, ..., Uk) (§5.1.10).

                    if (Ti == null) {
                        Set<ResolvedType> properUpperBounds = bounds.stream()
                                .filter(b -> b.isProperUpperBoundFor(alphaI).isPresent())
                                .map(b -> b.isProperUpperBoundFor(alphaI).get().getProperType())
                                .collect(Collectors.toSet());
                        if (properUpperBounds.size() == 0) {
                            throw new IllegalStateException();
                        }
                        Ti = glb(properUpperBounds);
                    }

                    newBounds = newBounds.withBound(new SameAsBound(alphaI, Ti));
                }

                //   The bounds α1 = T1, ..., αn = Tn are incorporated with the current bound set.

                BoundSet incorporatedBoundSet = this.incorporate(newBounds, typeSolver);

                //   If the result does not contain the bound false, then the result becomes the new bound set, and resolution
                //   proceeds by selecting a new set of variables to instantiate (if necessary), as described above.

                if (!incorporatedBoundSet.containsFalse()) {
                    return incorporatedBoundSet.performResolution(variablesToResolve, typeSolver);
                }

                //   Otherwise, the result contains the bound false, so a second attempt is made to instantiate { α1, ..., αn }
                //   by performing the step below.

                throw new UnsupportedOperationException();
            }

            // - If the bound set contains a bound of the form G<..., αi, ...> = capture(G<...>) for some i (1 ≤ i ≤ n), or;

            else {

                //   If the bound set produced in the step above contains the bound false;
                //
                //   then let Y1, ..., Yn be fresh type variables whose bounds are as follows:
                //
                //   - For all i (1 ≤ i ≤ n), if αi has one or more proper lower bounds L1, ..., Lk, then let the lower bound
                //     of Yi be lub(L1, ..., Lk); if not, then Yi has no lower bound.
                //
                //   - For all i (1 ≤ i ≤ n), where αi has upper bounds U1, ..., Uk, let the upper bound of Yi be
                //     glb(U1 θ, ..., Uk θ), where θ is the substitution [α1:=Y1, ..., αn:=Yn].
                //
                //   If the type variables Y1, ..., Yn do not have well-formed bounds (that is, a lower bound is not a subtype
                //   of an upper bound, or an intersection type is inconsistent), then resolution fails.
                //
                //   Otherwise, for all i (1 ≤ i ≤ n), all bounds of the form G<..., αi, ...> = capture(G<...>) are removed
                //   from the current bound set, and the bounds α1 = Y1, ..., αn = Yn are incorporated.
                //
                //   If the result does not contain the bound false, then the result becomes the new bound set, and resolution
                //   proceeds by selecting a new set of variables to instantiate (if necessary), as described above.
                //
                //   Otherwise, the result contains the bound false, and resolution fails.

                throw new UnsupportedOperationException();
            }
        }
        return Optional.empty();
    }

    private Set<Set<InferenceVariable>> allPossibleSetsWithProperty(Set<InferenceVariable> allElements, List<VariableDependency> dependencies) {
        Set<Set<InferenceVariable>> result = new HashSet<>();
        for (int i=1;i<=allElements.size();i++) {
            for (Set<InferenceVariable> aSubSet : buildAllSubsetsOfSize(allElements, i)){
                if (hasProperty(aSubSet, dependencies)) {
                    result.add(aSubSet);
                }
            }
        }
        return result;
    }

    private boolean thereAreProperSubsets(Set<InferenceVariable> aSet, Set<Set<InferenceVariable>> allPossibleSets) {
        for (Set<InferenceVariable> anotherSet : allPossibleSets) {
            if (!anotherSet.equals(aSet)) {
                if (isTheFirstAProperSubsetOfTheSecond(anotherSet, aSet)) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean isTheFirstAProperSubsetOfTheSecond(Set<InferenceVariable> subset, Set<InferenceVariable> originalSet) {
        return originalSet.containsAll(subset) && originalSet.size() > subset.size();
    }

    private Set<Set<InferenceVariable>> allSetsWithProperty(Set<InferenceVariable> allElements, List<VariableDependency> dependencies) {
        Set<Set<InferenceVariable>> allPossibleSets = allPossibleSetsWithProperty(allElements, dependencies);
        Set<Set<InferenceVariable>> selected = new HashSet<>();
        for (Set<InferenceVariable> aSet : allPossibleSets) {
            if (!thereAreProperSubsets(aSet, allPossibleSets)) {
                selected.add(aSet);
            }
        }
        return selected;
    }

    private boolean properUpperBoundsAreAtMostExceptionThrowableAndObject(InferenceVariable inferenceVariable) {
        throw new UnsupportedOperationException();
    }

    private boolean appearInLeftPartOfCapture(InferenceVariable inferenceVariable) {
        for (Bound b : bounds) {
            if (b instanceof CapturesBound) {
                CapturesBound capturesBound = (CapturesBound)b;
                if (capturesBound.getInferenceVariables().contains(inferenceVariable)) {
                    return true;
                }
            }
        }
        return false;
    }

    public List<Bound> getProperUpperBoundsFor(InferenceVariable inferenceVariable) {
        return bounds.stream().filter(b -> b.isProperUpperBoundFor(inferenceVariable).isPresent()).collect(Collectors.toList());
    }
}
