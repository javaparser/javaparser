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
 * This validator validates according to Java 11 syntax rules.
 */
public class Java11Validator extends Java10Validator {
    final Validator varAlsoInLambdaParameters = new SingleNodeTypeValidator<>(VarType.class, new VarValidator(true));

    public Java11Validator() {
        super();
        replace(varOnlyOnLocalVariableDefinitionAndForAndTry, varAlsoInLambdaParameters);
    }
}
