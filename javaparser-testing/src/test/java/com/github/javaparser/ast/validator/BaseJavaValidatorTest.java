package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class BaseJavaValidatorTest {
    @Test
    public void tryWithoutAnything() {
        ParseResult<Statement> result = new JavaParser().parse(STATEMENT, provider("try{}"));
        assertProblems(result, "(line 1,col 1) Try has no finally, no catch, and no resources.");
    }

    @Test
    public void classExtendingMoreThanOne() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X extends Y, Z {}"));
        assertProblems(result, "(line 1,col 20) A class cannot extend more than one other class.");
    }

    @Test
    public void interfaceUsingImplements() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("interface X implements Y {}"));
        assertProblems(result, "(line 1,col 24) An interface cannot implement other interfaces.");
    }

    @Test
    public void interfaceWithInitializer() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("interface X {{}}"));
        assertProblems(result, "(line 1,col 14) An interface cannot have initializers.");
    }

    @Test
    public void defaultMethodWithoutBody() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("interface X {default void a();}"));
        assertProblems(result, "(line 1,col 14) 'default' methods must have a body.");
    }

    @Test
    public void defaultInClass() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X {default void a(){};}"));
        assertProblems(result, "(line 1,col 10) 'default' is not allowed here.");
    }

    @Test
    public void localInterface() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X {void a(){interface I{}};}"));
        assertProblems(result, "(line 1,col 19) There is no such thing as a local interface.");
    }

}
