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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.observer.ObservableProperty;

class QualifiedProperty {
    private Class<? extends Node> containerClass;
    private ObservableProperty observableProperty;

    public Class<? extends Node> getContainerClass() {
        return containerClass;
    }

    public ObservableProperty getObservableProperty() {
        return observableProperty;
    }

    QualifiedProperty(Class<? extends Node> containerClass, ObservableProperty observableProperty) {
        this.containerClass = containerClass;
        this.observableProperty = observableProperty;
    }

    @Override
    public String toString() {
        return "QualifiedProperty{" +
                "containerClass=" + containerClass +
                ", observableProperty=" + observableProperty +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        QualifiedProperty that = (QualifiedProperty) o;

        if (!containerClass.getCanonicalName().equals(that.containerClass.getCanonicalName())) return false;
        return observableProperty == that.observableProperty;

    }

    @Override
    public int hashCode() {
        int result = containerClass.getCanonicalName().hashCode();
        result = 31 * result + observableProperty.hashCode();
        return result;
    }

    public TextElement[] separators() {
        if (this.equals(new QualifiedProperty(AnnotationDeclaration.class, ObservableProperty.MEMBERS))) {
            return new TextElement[]{};
        }
        return new TextElement[]{Tokens.comma(), Tokens.space()};
    }

    public boolean isInOwnLine() {
        if (this.equals(new QualifiedProperty(AnnotationDeclaration.class, ObservableProperty.MEMBERS))) {
            return true;
        }
        return false;
    }
}
