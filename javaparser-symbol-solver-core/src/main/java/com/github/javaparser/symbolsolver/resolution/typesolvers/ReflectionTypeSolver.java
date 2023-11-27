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

package com.github.javaparser.symbolsolver.resolution.typesolvers;

/**
 * Uses reflection to resolve types.
 * Classes on the classpath used to run your application will be found.
 * No source code is available for the resolved types.
 *
 * @author Federico Tomassetti
 */
public class ReflectionTypeSolver extends ClassLoaderTypeSolver {

    private final boolean jreOnly;

    /**
     * @param jreOnly if true, will only resolve types from the java or javax packages.
     * This is an easy way to say "I need a JRE to solve classes, and the one that is currently running is fine."
     * If false, will resolve any kind of type.
     */
    public ReflectionTypeSolver(boolean jreOnly) {
        super(ReflectionTypeSolver.class.getClassLoader());
        this.jreOnly = jreOnly;
    }

    /**
     * Resolves classes from the JRE that is currently running.
     * (It calls the other constructor with "true".)
     */
    public ReflectionTypeSolver() {
        this(true);
    }

    @Override
    protected boolean filterName(String name) {
        return !jreOnly || (name.startsWith("java.") || name.startsWith("javax."));
    }

}
