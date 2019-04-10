package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.*;

class TokenRangeTest {
    @Test
    void toStringWorks() {
        CompilationUnit cu = parse("class X {\n\tX(){\n// hello\n}\n}");
        assertEquals("X(){\n// hello\n}", cu.getClassByName("X").get().getDefaultConstructor().get().getTokenRange().get().toString());
    }

    @Test
    void renumberRangesWorks() {
        CompilationUnit cu = parse("class X {\n\tX(){\n// hello\n}\n}");

        assertEquals("1.1.5.1/6.1.6.1/7.1.7.1/8.1.8.1/9.1.9.1/10.1.10.1/1.2.1.2/2.2.2.2/3.2.3.2/4.2.4.2/5.2.5.2/6.2.6.2/1.3.9.3/1.4.1.4/2.4.2.4/1.5.1.5/1.5.1.5/", makeRangesString(cu));

        TokenRange tokenRange = cu.getTokenRange().get();
//        tokenRange.getBegin().insert(new JavaToken(1, "feif"));
//        tokenRange.getBegin().getNextToken().get().getNextToken().get().insert(new JavaToken(1, "faff"));
        cu.recalculatePositions();

        assertEquals("1.1.5.1/6.1.6.1/7.1.7.1/8.1.8.1/9.1.9.1/10.1.10.1/1.2.1.2/2.2.2.2/3.2.3.2/4.2.4.2/5.2.5.2/6.2.6.2/1.3.9.3/1.4.1.4/2.4.2.4/1.5.1.5/1.5.1.5/", makeRangesString(cu));
    }

    /**
     * Make a compact String for comparing token range positions.
     */
    private String makeRangesString(Node node) {
        Optional<JavaToken> token = node.getTokenRange().map(TokenRange::getBegin);
        StringBuilder result = new StringBuilder();
        while (token.isPresent()) {
            token = token.flatMap(t -> {
                result.append(t.getRange().map(r ->
                        r.begin.column + "." +
                                r.begin.line + "." +
                                r.end.column + "." +
                                r.end.line + "/"

                ).orElse("?"));
                return t.getNextToken();
            });
        }
        return result.toString();
    }
}