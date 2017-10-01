/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.resolution.declarations;

import com.github.javaparser.resolution.types.ResolvedType;

/**
 * A declaration of a method (either in an interface, a class, an enum or an annotation).
 *
 * @author Federico Tomassetti
 */
public interface ResolvedMethodDeclaration extends ResolvedMethodLikeDeclaration {

    /**
     * The type of the value returned by the current method. This method can also be invoked
     * for methods returning void.
     */
    ResolvedType getReturnType();

    /**
     * Is the method abstract? All interface methods not marked as default are abstract.
     */
    boolean isAbstract();

    /**
     * Is this a default method?
     */
    boolean isDefaultMethod();

    /*
     * Is this method static?
     */
    boolean isStatic();

}
