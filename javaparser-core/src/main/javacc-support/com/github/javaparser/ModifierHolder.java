/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Helper class for {@link GeneratedJavaParser}
 */
class ModifierHolder {
    final NodeList<Modifier> modifiers;
    final NodeList<AnnotationExpr> annotations;
    final JavaToken begin;

    ModifierHolder(JavaToken begin, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations) {
        this.begin = begin;
        this.modifiers = assertNotNull(modifiers);
        this.annotations = annotations;
    }
}
