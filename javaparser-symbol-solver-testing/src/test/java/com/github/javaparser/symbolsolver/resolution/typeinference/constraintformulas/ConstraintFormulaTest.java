package com.github.javaparser.symbolsolver.resolution.typeinference.constraintformulas;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typeinference.BoundSet;
import com.github.javaparser.symbolsolver.resolution.typeinference.ConstraintFormula;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariable;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.mock;

class ConstraintFormulaTest {

    private TypeSolver typeSolver = new ReflectionTypeSolver();
    private ResolvedType stringType = new ReferenceTypeImpl(new ReflectionTypeSolver().solveType(String.class.getCanonicalName()), typeSolver);

    /**
     * From JLS 18.1.2
     *
     * From Collections.singleton("hi"), we have the constraint formula ‹"hi" → α›.
     * Through reduction, this will become the constraint formula: ‹String <: α›.
     */
    @Test
    void testExpressionCompatibleWithTypeReduce1() {
        ResolvedTypeParameterDeclaration tp = mock(ResolvedTypeParameterDeclaration.class);

        Expression e = new StringLiteralExpr("hi");
        InferenceVariable inferenceVariable = new InferenceVariable("α", tp);

        ExpressionCompatibleWithType formula = new ExpressionCompatibleWithType(typeSolver, e, inferenceVariable);

        ConstraintFormula.ReductionResult res1 = formula.reduce(BoundSet.empty());
        assertEquals(
                ConstraintFormula.ReductionResult.empty().withConstraint(new TypeCompatibleWithType(typeSolver, stringType, inferenceVariable)),
                res1);

        assertEquals(
                ConstraintFormula.ReductionResult.empty().withConstraint(new TypeSubtypeOfType(typeSolver, stringType, inferenceVariable)),
                res1.getConstraint(0).reduce(BoundSet.empty()));
    }

//    /**
//     * From JLS 18.1.2
//     *
//     * From Arrays.asList(1, 2.0), we have the constraint formulas ‹1 → α› and ‹2.0 → α›. Through reduction,
//     * these will become the constraint formulas ‹int → α› and ‹double → α›, and then ‹Integer <: α› and ‹Double <: α›.
//     */
//    @Test
//    public void testExpressionCompatibleWithTypeReduce2() {
//        throw new UnsupportedOperationException();
//    }
//
//    /**
//     * From JLS 18.1.2
//     *
//     * From the target type of the constructor invocation List<Thread> lt = new ArrayList<>(), we have the constraint
//     * formula ‹ArrayList<α> → List<Thread>›. Through reduction, this will become the constraint formula ‹α <= Thread›,
//     * and then ‹α = Thread›.
//     */
//    @Test
//    public void testExpressionCompatibleWithTypeReduce3() {
//        throw new UnsupportedOperationException();
//    }
}
