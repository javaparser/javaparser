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

package com.github.javaparser.resolution;

/**
 * This exception is thrown when a symbol cannot be resolved.
 *
 * @author Federico Tomassetti
 */
public class UnsolvedSymbolException extends RuntimeException {

    /**
     * The name of the symbol that could not be resolved.
     */
    private String name;

    /**
     * Additional information that provides more details on the context that a symbol could not be resolved in, or
     * {@code null} if there is no contextual information, or if the contextual information is unknown.
     */
    private String context;

    /**
     * The throwable that caused this {@code UnsolvedSymbolException} to get thrown, or {@code null} if this
     * {@code UnsolvedSymbolException} was not caused by another throwable, or if the causative throwable is unknown.
     */
    private Throwable cause;

    public UnsolvedSymbolException(String name) {
        this(name, null, null);
    }

    public UnsolvedSymbolException(String name, String context) {
        this(name, context, null);
    }

    public UnsolvedSymbolException(String name, Throwable cause) {
        this(name, null, cause);
    }

    public UnsolvedSymbolException(String name, String context, Throwable cause) {
        super("Unsolved symbol" + (context != null ? " in " + context : "") + " : " + name, cause);
        this.name = name;
        this.context = context;
        this.cause = cause;
    }

    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        return "UnsolvedSymbolException{" +
               "context='" + context + "'" +
               ", name='" + name + "'" +
               ", cause='" + cause + "'" +
               "}";
    }
}
