package com.github.javaparser;

import com.github.javaparser.*;
import com.github.javaparser.ast.expr.Expression;
import org.junit.Test;

import java.util.Iterator;
import java.util.List;

import static com.github.javaparser.ASTParserConstants.*;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.Range.range;
import static org.junit.Assert.assertEquals;

public class JavaTokenTest {

    @Test
    public void testAFewTokens() {
        ParseResult<Expression> result = new JavaParser().parse(ParseStart.EXPRESSION, provider("1 +/*2*/1 "));
        List<JavaToken> tokens = result.getTokens().get();
        Iterator<JavaToken> iterator = tokens.iterator();
        assertToken("1", range(1, 1, 1, 1), INTEGER_LITERAL, iterator.next());
        assertToken(" ", range(1, 2, 1, 2), 1, iterator.next());
        assertToken("+", range(1, 3, 1, 3), PLUS, iterator.next());
        assertToken("/*2*/", range(1, 4, 1, 8), MULTI_LINE_COMMENT, iterator.next());
        assertToken("1", range(1, 9, 1, 9), INTEGER_LITERAL, iterator.next());
        assertToken(" ", range(1, 10, 1, 10), 1, iterator.next());
        assertToken("", range(1, 10, 1, 10), EOF, iterator.next());
        assertEquals(false, iterator.hasNext());
    }

    private void assertToken(String image, Range range, int kind, JavaToken token) {
        assertEquals(image, token.getText());
        assertEquals(range, token.getRange());
        assertEquals(kind, token.getKind());
    }
}
