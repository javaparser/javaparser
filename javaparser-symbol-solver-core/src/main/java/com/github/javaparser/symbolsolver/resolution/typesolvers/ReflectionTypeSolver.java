/*
 * Copyright (C) 2016-2018 The JavaParser Team.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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
