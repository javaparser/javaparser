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

package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.utils.Utils;

import static com.github.javaparser.utils.Utils.assertNonEmpty;

/**
 * A literal string.
 * <br/><code>"Hello World!"</code>
 * <br/><code>"\"\n"</code>
 * <br/><code>"\u2122"</code>
 * <br/><code>"💩"</code>
 *
 * @author Julio Vilmar Gesser
 */
public class StringLiteralExpr extends LiteralExpr {

    protected String value;

    public StringLiteralExpr() {
        this(null, "empty");
    }

    public StringLiteralExpr(final String value) {
        this(null, value);
    }

    /**
     * Utility method that creates a new StringLiteralExpr. Escapes EOL characters.
     */
    public static StringLiteralExpr escape(String string) {
        return new StringLiteralExpr(Utils.escapeEndOfLines(string));
    }

    public StringLiteralExpr(final Range range, final String value) {
        super(range);
        assertNonEmpty(value);
        setValue(value);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public final String getValue() {
        return value;
    }

    public final StringLiteralExpr setValue(final String value) {
        notifyPropertyChange(ObservableProperty.VALUE, this.value, value);
        this.value = assertNonEmpty(value);
        if (value.contains("\n") || value.contains("\r")) {
            throw new IllegalArgumentException("Illegal literal expression: newlines (line feed or carriage return) have to be escaped");
        }
        return this;
    }
}
