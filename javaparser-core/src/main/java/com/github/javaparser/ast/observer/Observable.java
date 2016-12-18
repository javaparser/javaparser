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

package com.github.javaparser.ast.observer;

/**
 * Observable element.
 */
public interface Observable {

    /**
     * Register an observer.
     */
    void register(AstObserver observer);

    /**
     * Unregister an observer. If the given observer was not registered there are no effects.
     */
    void unregister(AstObserver observer);

    /**
     * Was this observer registered?
     * Note that equals is used to determine if the given observer was registered.
     */
    boolean isRegistered(AstObserver observer);
}
