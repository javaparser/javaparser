package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.junit.jupiter.api.Test;

import java.util.function.Supplier;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static org.junit.jupiter.api.Assertions.*;

abstract class AbstractTypeSolverTest<T extends TypeSolver> extends AbstractSymbolResolutionTest {

    private final Supplier<T> solverSupplier;

    /**
     * Create new tests for the type solver.
     *
     * @param solverSupplier The supplier of solvers
     */
    public AbstractTypeSolverTest(Supplier<T> solverSupplier) {
        this.solverSupplier = solverSupplier;
    }

    /**
     * Get the supplier of solvers.
     *
     * @return The supplier.
     */
    public Supplier<T> getSolverSupplier() {
        return solverSupplier;
    }

    /**
     * Setting self as parent should throw an {@link IllegalArgumentException}.
     */
    @Test
    void tryingToSetParentAsSelfShouldThrowIllegalStateException() {
        TypeSolver solver = createTypeSolver();
        assertThrows(IllegalStateException.class, () -> solver.setParent(solver));
    }

    /**
     * Setting a parent when a type solver already has a parent should throw an {@link IllegalArgumentException}.
     */
    @Test
    void tryingToSetParentIfParentAlreadyDefinedShouldThrowIllegalStateException() {
        TypeSolver parentSolver = createTypeSolver();
        TypeSolver solver = createTypeSolver();
        solver.setParent(parentSolver);

        assertThrows(IllegalStateException.class, () -> solver.setParent(parentSolver));
    }

    /**
     * When a {@link com.github.javaparser.symbolsolver.model.resolution.TypeSolver} don't have a parent it should return
     * {@code null}.
     * After setting a parent using {@link com.github.javaparser.symbolsolver.model.resolution.TypeSolver#setParent(TypeSolver)}
     * the method {@link TypeSolver#getParent()} should return the value set.
     */
    @Test
    void whenParentIsSetItShouldBeReturnedWithGetParent() {
        TypeSolver solver = createTypeSolver();
        assertNull(solver.getParent());

        TypeSolver parentSolver = createTypeSolver();
        solver.setParent(parentSolver);
        TypeSolver returnedSolver = solver.getParent();
        assertNotNull(returnedSolver);
        assertEquals(parentSolver, returnedSolver);
    }

    /**
     * Create a new instance of {@link T}.
     *
     * @return The newly created {@see T}
     */
    public T createTypeSolver() {
        return getSolverSupplier().get();
    }

}
