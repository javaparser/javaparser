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

package com.github.javaparser.ast;

/**
 * A key to a piece of data associated with a {@link Node} at runtime.
 * The key contains type information that can be used to check the
 * type of any user data value for the key when the value is set. DataKey is abstract in order to
 * force the creation of a subtype. That subtype is used to test for identity when looking for the
 * user data because actual object identity would suffer from problems under serialization.
 * So, the correct way to declare a DataKey is like this:
 * <p>
 * <pre>
 * <code>
 * public static final DataKey&lt;Role&gt; ROLE = new DataKey&lt;Role&gt;() { };
 * </code>
 * </pre>
 * <p>
 * This code was taken from the <a href="http://wicket.apache.org/">Wicket project</a>.
 *
 * @param <T> The type of the object which is stored
 * @see Node#getData(DataKey)
 */
public abstract class DataKey<T> {
    @Override
    public int hashCode() {
        return getClass().hashCode();
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return obj != null && getClass().equals(obj.getClass());
    }
}
