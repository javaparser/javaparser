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

/**
 * Suggestion to upgrade the Java language level.
 * A message that can be used to tell the user that a feature is
 * not available in the configured language level.
 *
 * @since 3.24.5
 */
public final class UpgradeJavaMessage {

    /**
     * The reason why the language level must be upgraded.
     */
    private final String reason;

    /**
     * The language level that must be configured.
     */
    private final ParserConfiguration.LanguageLevel level;

    /**
     * Contructor.
     * @param reason The reason why the language level must be upgraded.
     * @param level The language level that must be configured.
     */
    UpgradeJavaMessage(
        final String reason,
        final ParserConfiguration.LanguageLevel level
    ) {
        this.reason = reason;
        this.level = level;
    }

    @Override
    public String toString() {
        return String.format(
            "%s Pay attention that this feature is supported starting from '%s' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.",
            this.reason,
            this.level.toString()
        );
    }
}
