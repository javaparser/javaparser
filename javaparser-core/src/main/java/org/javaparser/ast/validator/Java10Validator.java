/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package org.javaparser.ast.validator;

import org.javaparser.ast.type.VarType;
import org.javaparser.ast.validator.chunks.VarValidator;

/**
 * This validator validates according to Java 10 syntax rules.
 */
public class Java10Validator extends Java9Validator {

    final Validator varOnlyOnLocalVariableDefinitionAndForAndTry = new SingleNodeTypeValidator<>(VarType.class, new VarValidator(false));

    public Java10Validator() {
        super();
        add(varOnlyOnLocalVariableDefinitionAndForAndTry);
        /* There is no validator that validates that "var" is not used in Java 9 and lower, since the parser will never create a VarType node,
           because that is done by the Java10 postprocessor. You can add it by hand, but that is obscure enough to ignore. */
    }
}
