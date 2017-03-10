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

public class BaseJavaValidatorTest {
    @Test
    public void tryWithoutAnything() {
        ParseResult<Statement> result = new JavaParser().parse(STATEMENT, provider("try{}"));
        assertEquals("[(line 1,col 1) Try has no finally, no catch, and no resources.]", result.getProblems().toString());
    }

    @Test
    public void classExtendingMoreThanOne() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X extends Y, Z {}"));
        assertEquals("[(line 1,col 20) A class cannot extend more than one other class.]", result.getProblems().toString());
    }

    @Test
    public void interfaceUsingImplements() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("interface X implements Y {}"));
        assertEquals("[(line 1,col 24) An interface cannot implement other interfaces.]", result.getProblems().toString());
    }

    @Test
    public void interfaceWithInitializer() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("interface X {{}}"));
        assertEquals("[(line 1,col 14) An interface cannot have initializers.]", result.getProblems().toString());
    }

    @Test
    public void defaultMethodWithoutBody() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("interface X {default void a();}"));
        assertEquals("[(line 1,col 22) 'default' methods must have a body.]", result.getProblems().toString());
    }

    @Test
    public void defaultInClass() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X {default void a(){};}"));
        assertEquals("[(line 1,col 18) A class cannot have default members.]", result.getProblems().toString());
    }

    @Test
    public void localInterface() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X {void a(){interface I{}};}"));
        assertEquals("[(line 1,col 19) There is no such thing as a local interface.]", result.getProblems().toString());
    }

}
