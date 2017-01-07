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

package com.github.javaparser.javadoc;

import java.util.Optional;

public class JavadocDocument {
    private JavadocText summary;
    private Optional<JavadocText> details;

    public JavadocDocument(JavadocText summary) {
        this.summary = summary;
        this.details = Optional.empty();
    }

    @Override
    public String toString() {
        return "JavadocDocument{" +
                "summary=" + summary +
                ", details=" + details +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavadocDocument document = (JavadocDocument) o;

        if (!summary.equals(document.summary)) return false;
        return details.equals(document.details);

    }

    @Override
    public int hashCode() {
        int result = summary.hashCode();
        result = 31 * result + details.hashCode();
        return result;
    }
}
