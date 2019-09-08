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

package com.github.javaparser;

import com.github.javaparser.ast.expr.Expression;
import org.junit.jupiter.api.Test;

import java.util.Iterator;

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.JavaToken.Category.*;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.Range.range;
import static org.junit.jupiter.api.Assertions.*;

class JavaTokenTest {

    @Test
    void testAFewTokens() {
        ParseResult<Expression> result = new JavaParser().parse(ParseStart.EXPRESSION, provider("1 +/*2*/1 "));
        Iterator<JavaToken> iterator = result.getResult().get().getTokenRange().get().iterator();
        assertToken("1", range(1, 1, 1, 1), INTEGER_LITERAL, LITERAL, iterator.next());
        assertToken(" ", range(1, 2, 1, 2), SPACE, WHITESPACE_NO_EOL, iterator.next());
        assertToken("+", range(1, 3, 1, 3), PLUS, OPERATOR, iterator.next());
        assertToken("/*2*/", range(1, 4, 1, 8), MULTI_LINE_COMMENT, COMMENT, iterator.next());
        assertToken("1", range(1, 9, 1, 9), INTEGER_LITERAL, LITERAL, iterator.next());
        assertToken(" ", range(1, 10, 1, 10), SPACE, WHITESPACE_NO_EOL, iterator.next());
        assertToken("", range(1, 10, 1, 10), EOF, WHITESPACE_NO_EOL, iterator.next());
        assertFalse(iterator.hasNext());
    }

    private void assertToken(String image, Range range, int kind, JavaToken.Category category, JavaToken token) {
        assertEquals(image, token.getText());
        assertEquals(range, token.getRange().get());
        assertEquals(kind, token.getKind());
        assertEquals(category, token.getCategory());
        token.getNextToken().ifPresent(nt -> assertEquals(token, nt.getPreviousToken().get()));
        token.getPreviousToken().ifPresent(pt -> assertEquals(token, pt.getNextToken().get()));
        assertTrue(token.getNextToken().isPresent() || token.getPreviousToken().isPresent());
    }

    @Test
    void testAFewImagesForTokenKinds() {
        assertEquals("=", new JavaToken(ASSIGN).getText());
        // TODO this shouldn't be a space.
        assertEquals(" ", new JavaToken(EOF).getText());
        assertEquals("*/", new JavaToken(JAVADOC_COMMENT).getText());
    }

    @Test
    void testKindEnum() {
        JavaToken.Kind kind = JavaToken.Kind.valueOf(GeneratedJavaParserConstants.ASSERT);

        assertEquals(JavaToken.Kind.ASSERT, kind);
        assertEquals(GeneratedJavaParserConstants.ASSERT, kind.getKind());
    }
}
