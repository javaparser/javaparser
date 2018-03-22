package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ParserConfigurationTest {
    @Test
    public void storeNoTokens() {
        ParseResult<CompilationUnit> result = new JavaParser(new ParserConfiguration().setStoreTokens(false)).parse(ParseStart.COMPILATION_UNIT, provider("class X{}"));

        assertFalse(result.getResult().get().getTokenRange().isPresent());
        assertTrue(result.getResult().get().findAll(Node.class).stream().noneMatch(node -> node.getTokenRange().isPresent()));
    }

    @Test
    public void noProblemsHere() {
        ParseResult<Statement> result =
                new JavaParser(new ParserConfiguration().setLanguageLevel(RAW))
                        .parse(STATEMENT, provider("try{}"));
        assertEquals(true, result.isSuccessful());
    }


}
