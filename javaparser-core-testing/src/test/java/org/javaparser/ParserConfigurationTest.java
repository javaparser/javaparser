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

package org.javaparser;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.Node;
import org.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static org.javaparser.ParseStart.STATEMENT;
import static org.javaparser.ParserConfiguration.LanguageLevel.*;
import static org.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ParserConfigurationTest {
    @Test
    void storeNoTokens() {
        ParseResult<CompilationUnit> result = new JavaParser(new ParserConfiguration().setStoreTokens(false)).parse(ParseStart.COMPILATION_UNIT, provider("class X{}"));

        assertFalse(result.getResult().get().getTokenRange().isPresent());
        assertTrue(result.getResult().get().findAll(Node.class).stream().noneMatch(node -> node.getTokenRange().isPresent()));
    }

    @Test
    void noProblemsHere() {
        ParseResult<Statement> result =
                new JavaParser(new ParserConfiguration().setLanguageLevel(RAW))
                        .parse(STATEMENT, provider("try{}"));
        assertTrue(result.isSuccessful());
    }


}
