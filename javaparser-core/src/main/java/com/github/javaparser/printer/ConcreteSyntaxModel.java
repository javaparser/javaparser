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

package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;

import java.util.List;

/**
 * The Concrete Syntax Model for a single node type. It knows the syntax used to represent a certain element in Java
 * code.
 */
public class ConcreteSyntaxModel {

    interface Element {

    }

    class StringElement implements Element {
        private int tokenType;
        private String content;
    }

    class ChildElement implements Element {
        private ObservableProperty property;
    }

    class ListElement implements Element {
        private ObservableProperty property;
        private StringElement separator;
    }

    public List<Element> getElements() {
        throw new UnsupportedOperationException();
    }

    private ConcreteSyntaxModel() {

    }

    public static ConcreteSyntaxModel forClass(Class<? extends Node> nodeClazz) {
        throw new UnsupportedOperationException();
    }

}
