package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.assertEquals;

public class DefaultValidatorTest {
    @Test
    public void tryWithoutAnything() {
        ParseResult<Statement> result = new JavaParser().parse(ParseStart.STATEMENT, provider("try{}"), new DefaultValidator());
        assertEquals("[(line 1,col 1) Try has no finally, no catch, and no resources]", result.getProblems().toString());
    }
    @Test
    public void classExtendingMoreThanOne() {
        ParseResult<Statement> result = new JavaParser().parse(ParseStart.STATEMENT, provider("try{}"), new DefaultValidator());
        assertEquals("[(line 1,col 1) Try has no finally, no catch, and no resources]", result.getProblems().toString());
    }

}
