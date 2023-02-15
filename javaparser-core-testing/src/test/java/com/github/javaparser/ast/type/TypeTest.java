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

package com.github.javaparser.ast.type;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.validator.language_level_validations.Java5Validator;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.VARIABLE_DECLARATION_EXPR;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.RAW;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.StaticJavaParser.parseType;
import static com.github.javaparser.StaticJavaParser.parseVariableDeclarationExpr;
import static org.junit.jupiter.api.Assertions.*;

class TypeTest {
    @Test
    void asString() {
        assertEquals("int", typeAsString("int x"));
        assertEquals("List<Long>", typeAsString("List<Long> x"));
        assertEquals("String", typeAsString("@A String x"));
        assertEquals("List<? extends Object>", typeAsString("List<? extends Object> x"));
    }

    @Test
    void primitiveTypeArgumentDefaultValidator() {
        assertThrows(ParseProblemException.class, () -> typeAsString("List<long> x;"));
    }

    @Test
    void primitiveTypeArgumentLenientValidator() {
        ParserConfiguration config = new ParserConfiguration()
                .setLanguageLevel(RAW);
        config.getProcessors().add(() -> new Java5Validator() {{
            remove(noPrimitiveGenericArguments);
        }}.processor());

        ParseResult<VariableDeclarationExpr> result = new JavaParser(config).parse(
                VARIABLE_DECLARATION_EXPR, provider("List<long> x"));
        assertTrue(result.isSuccessful());

        VariableDeclarationExpr decl = result.getResult().get();
        assertEquals("List<long>", decl.getVariable(0).getType().asString());
    }

    private String typeAsString(String s) {
        return parseVariableDeclarationExpr(s).getVariable(0).getType().asString();
    }

    @Test
    void arrayType() {
        Type type = parseType("int[]");
        assertTrue(type.isArrayType());
        ArrayType arrayType = type.asArrayType();
        final ArrayType[] s = new ArrayType[1];
        type.ifArrayType(t -> s[0] = t);
        assertNotNull(s[0]);
    }

    @Test
    void issue1251() {
        final Type type = parseType("TypeUtilsTest<String>.Tester");
        assertEquals("TypeUtilsTest<String>.Tester", type.toString());
    }

}
