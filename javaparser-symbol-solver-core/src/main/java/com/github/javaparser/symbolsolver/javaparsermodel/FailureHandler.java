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

package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.resolution.UnsolvedSymbolException;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/*
 * This class allows exceptions to be handled either by casting particular exceptions 
 * or by throwing new runtime exceptions.
 */
public class FailureHandler {

    private static final Map<Class<? extends Throwable>, Function<Throwable, ? extends RuntimeException>> FAILURE_CONVERTER = new HashMap<>();
    static {
        FAILURE_CONVERTER.put(UnsolvedSymbolException.class,
                (Throwable th) -> (RuntimeException)th);
    }

    public RuntimeException handle(Throwable th) {
        return handle(th, null);
    }
                                   
    public RuntimeException handle(Throwable th, String message) {
        // searching for exact mapping
        Function<Throwable, ? extends RuntimeException> converter = FAILURE_CONVERTER.get(findRootCause(th).getClass());
        if (converter != null) {
            return converter.apply(th);
        }
        // handle runtime exceptions
        if (RuntimeException.class.isAssignableFrom(th.getClass())) {
            return (RuntimeException) th;
        }
        return getRuntimeExceptionFrom(findRootCause(th), message);
    }

    protected final <E extends Throwable> E findRootCause(Throwable failure) {
        while (failure != null) {
            if (isRootCause(failure)) {
                return (E) failure;
            }
            failure = failure.getCause();
        }
        return null;
    }

    private boolean isRootCause(Throwable th) {
        return th.getCause() == null;
    }
    
    private RuntimeException getRuntimeExceptionFrom(Throwable th, String message) {
        if (message == null || message.isEmpty())
            return new RuntimeException(findRootCause(th));
        return new RuntimeException(message, findRootCause(th));
    }

}
