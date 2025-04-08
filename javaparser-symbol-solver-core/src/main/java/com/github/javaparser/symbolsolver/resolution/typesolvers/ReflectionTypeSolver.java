/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

import java.util.function.Predicate;
import java.util.stream.Stream;

/**
 * Uses reflection to resolve types.
 * Classes on the classpath used to run your application will be found.
 * No source code is available for the resolved types.
 *
 * @author Federico Tomassetti
 */
public class ReflectionTypeSolver extends ClassLoaderTypeSolver {
    private final Predicate<String> classFilter;
    /**
     * Class name filter matching all classes.
     */
    public static final Predicate<String> ALL_CLASSES = name -> true;
    /**
     * Class name filter matching classes in the core Java standard library.
     * This includes everything under {@code java.} and {@code javax.}.
     */
    public static final Predicate<String> JRE_ONLY = name -> name.startsWith("java.") || name.startsWith("javax.");
    /**
     * Class name filter matching classes in the Java Class Library.
     * The Java Class Library is the Java standard library; this filter includes all
     * packages listed in the {@code java.se} module of Java 21, as well as
     * {@code java.corba} as of Java 9. In this way, it encompasses the JCL of all
     * Java version from Java 8 to 21.
     */
    public static final Predicate<String> JCL_ONLY = name -> Stream.of(
                    "java.",
                    "javax.",
                    "org.ietf.jgss.",
                    "org.omg.COBRA.",
                    "org.omg.COBRA_2_3.",
                    "org.omg.CosNaming.",
                    "org.omg.Dynamic.",
                    "org.omg.DynamicAny.",
                    "org.omg.IOP.",
                    "org.omg.Messaging.",
                    "org.omg.PortableInterceptor.",
                    "org.omg.PortableServer.",
                    "org.omg.stub.java.rmi.",
                    "org.w3c.dom.",
                    "org.xml.sax.")
            .anyMatch(name::startsWith);

    /**
     * @param classFilter a name-based filter indicating which types to resolve.
     *                    Similarily to {@link ReflectionTypeSolver(boolean)}, this allows you to specify "I need to resolve certain classes (like the Java standard library), and whatever is available on the classpath is fine.".
     * @see #ALL_CLASSES
     * @see #JRE_ONLY
     * @see #JCL_ONLY
     */
    public ReflectionTypeSolver(Predicate<String> classFilter) {
        super(ReflectionTypeSolver.class.getClassLoader());
        this.classFilter = classFilter;
    }

    /**
     * @param jreOnly if true, will only resolve types from the java or javax packages.
     * This is an easy way to say "I need a JRE to solve classes, and the one that is currently running is fine."
     * If false, will resolve any kind of type.
     */
    public ReflectionTypeSolver(boolean jreOnly) {
        this(jreOnly ? JRE_ONLY : ALL_CLASSES);
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
        return classFilter.test(name);
    }
}
