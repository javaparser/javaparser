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

package com.github.javaparser.ast.visitor;

public interface Visitable {
    /**
     * Accept method for visitor support.
     *
     * @param <R> the type of the return value of the visitor
     * @param <A> the type the user argument passed to the visitor
     * @param v the visitor implementation
     * @param arg the argument passed to the visitor (of type A)
     * @return the result of the visit (of type R)
     */
    <R, A> R accept(GenericVisitor<R, A> v, A arg);

    /**
     * Accept method for visitor support.
     *
     * @param <A> the type the argument passed for the visitor
     * @param v the visitor implementation
     * @param arg any value relevant for the visitor (of type A)
     */
    <A> void accept(VoidVisitor<A> v, A arg);
}
