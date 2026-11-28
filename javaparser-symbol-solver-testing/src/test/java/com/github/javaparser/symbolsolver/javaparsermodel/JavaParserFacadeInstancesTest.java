/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.fail;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.lang.ref.WeakReference;
import java.util.Arrays;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.parallel.Execution;
import org.junit.jupiter.api.parallel.ExecutionMode;

/**
 * Regression tests for the static {@code JavaParserFacade} instance cache (issue #5236).
 * <p>
 * Surefire runs methods of a class in parallel; keep these sequential so
 * {@link JavaParserFacade#clearInstances()} cannot race the reachability checks.
 */
@Execution(ExecutionMode.SAME_THREAD)
class JavaParserFacadeInstancesTest {

    @AfterAll
    static void tearDown() {
        JavaParserFacade.clearInstances();
    }

    @Test
    void getReturnsTheSameFacadeWhileSolverAndFacadeAreReachable() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade first = JavaParserFacade.get(typeSolver);
        JavaParserFacade second = JavaParserFacade.get(typeSolver);
        assertNotNull(first);
        assertSame(first, second);
        assertSame(typeSolver, first.getTypeSolver());
    }

    @Test
    void getReturnsALiveFacadeAfterClearInstances() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade beforeClear = JavaParserFacade.get(typeSolver);
        JavaParserFacade.clearInstances();
        JavaParserFacade afterClear = JavaParserFacade.get(typeSolver);
        assertNotNull(afterClear);
        assertNotSame(beforeClear, afterClear);
        assertSame(typeSolver, afterClear.getTypeSolver());
    }

    @Test
    void unreferencedTypeSolverAndFacadeBecomeCollectable() throws InterruptedException {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade facade = JavaParserFacade.get(typeSolver);
        WeakReference<TypeSolver> solverRef = new WeakReference<>(typeSolver);
        WeakReference<JavaParserFacade> facadeRef = new WeakReference<>(facade);
        typeSolver = null;
        facade = null;

        assertGarbageCollected(solverRef);
        assertGarbageCollected(facadeRef);
    }

    @Test
    void getRecreatesAFacadeIfThePreviousOneWasCollected() throws InterruptedException {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade first = JavaParserFacade.get(typeSolver);
        WeakReference<JavaParserFacade> firstRef = new WeakReference<>(first);
        first = null;

        assertGarbageCollected(firstRef);

        JavaParserFacade recreated = JavaParserFacade.get(typeSolver);
        assertNotNull(recreated);
        assertSame(typeSolver, recreated.getTypeSolver());
    }

    private static void assertGarbageCollected(WeakReference<?> ref) throws InterruptedException {
        for (int i = 0; i < 50; i++) {
            System.gc();
            System.runFinalization();
            if (ref.get() == null) {
                return;
            }
            byte[] pressure = new byte[1024 * 1024];
            Arrays.fill(pressure, (byte) 1);
            Thread.sleep(20);
        }
        fail("object was still reachable from JavaParserFacade.instances");
    }
}
