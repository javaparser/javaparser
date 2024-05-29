/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.validator.SimpleValidator;
import com.github.javaparser.ast.validator.Validator;

/**
 * This validator validates according to Java 17 syntax rules.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/17/">https://openjdk.java.net/projects/jdk/17/</a>
 */
public class Java17Validator extends Java16Validator {

	final Validator sealedNotAllowedAsIdentifier = new SimpleValidator<>(ClassOrInterfaceDeclaration.class, n -> n.getName().getIdentifier().equals("sealed"), (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("'sealed' identifier is not authorised in this context.", ParserConfiguration.LanguageLevel.JAVA_17)));
	final Validator permitsNotAllowedAsIdentifier = new SimpleValidator<>(ClassOrInterfaceDeclaration.class, n -> n.getName().getIdentifier().equals("permits"), (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("'permits' identifier is not authorised in this context.", ParserConfiguration.LanguageLevel.JAVA_17)));

    public Java17Validator() {
        super();
        // Released Language Features
        // Sealed Classes - https://openjdk.java.net/jeps/409
        add(sealedNotAllowedAsIdentifier);
        add(permitsNotAllowedAsIdentifier);
        remove(noSealedClasses);
        remove(noPermitsListInClasses);
    }
}
