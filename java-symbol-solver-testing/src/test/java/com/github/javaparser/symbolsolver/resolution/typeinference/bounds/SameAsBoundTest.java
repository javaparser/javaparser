package com.github.javaparser.symbolsolver.resolution.typeinference.bounds;

import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typeinference.Bound;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariable;
import com.github.javaparser.symbolsolver.resolution.typeinference.Instantiation;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;

public class SameAsBoundTest {

    private TypeSolver typeSolver = new ReflectionTypeSolver();
    private ResolvedType stringType = new ReferenceTypeImpl(new ReflectionTypeSolver().solveType(String.class.getCanonicalName()), typeSolver);

    @Test
    public void recognizeInstantiation() {
        // { α = String } contains a single bound, instantiating α as String.
        InferenceVariable inferenceVariable = new InferenceVariable("α", null);
        Bound bound1 = new SameAsBound(inferenceVariable, stringType);
        Bound bound2 = new SameAsBound(stringType, inferenceVariable);

        assertEquals(Optional.of(new Instantiation(inferenceVariable, stringType)), bound1.isAnInstantiation());
        assertEquals(Optional.of(new Instantiation(inferenceVariable, stringType)), bound2.isAnInstantiation());
    }

}
