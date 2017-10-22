package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.UnionType;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.EXPRESSION;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertCollections;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java7ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java7Validator()));

    @Test
    public void generics() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X<A>{List<String> b = new ArrayList<>();}"));
        assertNoProblems(result);
    }

    @Test
    public void defaultMethodWithoutBody() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X {default void a();}"));
        assertProblems(result, "(line 1,col 14) 'default' is not allowed here.");
    }

    @Test
    public void tryWithoutAnything() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try{}"));
        assertProblems(result, "(line 1,col 1) Try has no finally, no catch, and no resources.");
    }

    @Test
    public void tryWithResourceVariableDeclaration() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try(Reader r = new Reader()){}"));
        assertNoProblems(result);
    }

    @Test
    public void tryWithResourceReference() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try(a.b.c){}"));
        assertProblems(result, "(line 1,col 1) Try with resources only supports variable declarations.");
    }

    @Test
    public void stringsInSwitch() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case \"abc\": ;}"));
        assertNoProblems(result);
    }

    @Test
    public void binaryIntegerLiterals() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("0b01"));
        assertNoProblems(result);
    }

    @Test
    public void underscoresInIntegerLiterals() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("1_000_000"));
        assertNoProblems(result);
    }

    @Test
    public void multiCatch() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try{}catch(Abc|Def e){}"));
        assertNoProblems(result);
    }

    @Test
    public void multiCatchWithoutElements() {
        UnionType unionType = new UnionType();

        List<Problem> problems = new ArrayList<>();
        javaParser.getParserConfiguration().getValidator().accept(unionType, new ProblemReporter(problems));
        
        assertProblems(problems, "UnionType.elements can not be empty.");
    }

    @Test
    public void multiCatchWithOneElement() {
        UnionType unionType = new UnionType();
        unionType.getElements().add(new ClassOrInterfaceType());

        List<Problem> problems = new ArrayList<>();
        javaParser.getParserConfiguration().getValidator().accept(unionType, new ProblemReporter(problems));
        
        assertProblems(problems, "Union type (multi catch) must have at least two elements.");
    }

    @Test
    public void noLambdas() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("a(() -> 1);"));
        assertProblems(result, "(line 1,col 3) Lambdas are not supported.");
    }
}
