package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.assertEquals;

public class DefaultValidatorTest {
    @Test
    public void tryWithoutAnything() {
        ParseResult<Statement> result = new JavaParser().parse(STATEMENT, provider("try{}"), new DefaultValidator());
        assertEquals("[(line 1,col 1) Try has no finally, no catch, and no resources]", result.getProblems().toString());
    }

    @Test
    public void classExtendingMoreThanOne() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X extends Y, Z {}"), new DefaultValidator());
        assertEquals("[(line 1,col 20) A class cannot extend more than one other class]", result.getProblems().toString());
    }

    @Test
    public void interfaceUsingImplements() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("interface X implements Y {}"), new DefaultValidator());
        assertEquals("[(line 1,col 24) An interface cannot implement other interfaces]", result.getProblems().toString());
    }

}
