/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
package com.github.javaparser.ast.validator.language_level_validations;

import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.Validator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.VarValidator;

/**
 * This validator validates according to Java 11 syntax rules.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/11/">https://openjdk.java.net/projects/jdk/11/</a>
 */
public class Java11Validator extends Java10Validator {

    final Validator varAlsoInLambdaParameters = new SingleNodeTypeValidator<>(VarType.class, new VarValidator(true));

    public Java11Validator() {
        super();
        {
            /*
             * Java 10 released local variable type inference in for and try-with (JEP286).
             * Java 11 released local variable type inference for lambda parameters also (JEP323)
             */
            replace(varOnlyOnLocalVariableDefinitionAndForAndTry, varAlsoInLambdaParameters);
        }
    }
}
