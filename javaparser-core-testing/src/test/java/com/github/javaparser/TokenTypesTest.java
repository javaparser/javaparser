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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.SwitchEntry;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.utils.CodeGenerationUtils.mavenModuleRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public class TokenTypesTest {

    @Test
    void everyTokenHasACategory() throws IOException {
        final int tokenCount = GeneratedJavaParserConstants.tokenImage.length;
        Path tokenTypesPath = mavenModuleRoot(JavaParserTest.class).resolve("../javaparser-core/src/main/java/com/github/javaparser/TokenTypes.java");
        CompilationUnit tokenTypesCu = parse(tokenTypesPath);

        // -1 to take off the default: case.
        int switchEntries = tokenTypesCu.findAll(SwitchEntry.class).size() - 1;

        // The amount of "case XXX:" in TokenTypes.java should be equal to the amount of tokens JavaCC knows about:
        assertEquals(tokenCount, switchEntries);
    }

    @Test
    void throwOnUnrecognisedTokenType() {
        assertThrows(AssertionError.class, () -> {
            TokenTypes.getCategory(-1);
        });
    }

}
