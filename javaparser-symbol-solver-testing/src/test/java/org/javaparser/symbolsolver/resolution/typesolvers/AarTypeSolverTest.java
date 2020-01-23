/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package org.javaparser.symbolsolver.resolution.typesolvers;

import org.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

class AarTypeSolverTest extends AbstractSymbolResolutionTest {

    @Test
    void initial() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/aars/support-compat-24.2.0.aar");
        AarTypeSolver aarTypeSolver = new AarTypeSolver(pathToJar);
        assertEquals(true, aarTypeSolver.tryToSolveType("android.support.v4.app.ActivityCompat").isSolved());
        assertEquals(true, aarTypeSolver.tryToSolveType("android.support.v4.app.ActivityManagerCompat").isSolved());
        assertEquals(true, aarTypeSolver.tryToSolveType("android.support.v4.app.NotificationCompat").isSolved());
        assertEquals(true, aarTypeSolver.tryToSolveType("android.support.v4.app.NotificationCompat.Action").isSolved());
        assertEquals(true, aarTypeSolver.tryToSolveType("android.support.v4.app.NotificationCompat.Action.Builder").isSolved());
        assertEquals(false, aarTypeSolver.tryToSolveType("org.javaparser.ASTParser.Foo").isSolved());
        assertEquals(false, aarTypeSolver.tryToSolveType("org.javaparser.Foo").isSolved());
        assertEquals(false, aarTypeSolver.tryToSolveType("Foo").isSolved());
    }

}
