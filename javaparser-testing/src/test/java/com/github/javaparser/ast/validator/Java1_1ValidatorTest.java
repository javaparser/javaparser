package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.EXPRESSION;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java1_1ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java1_1Validator()));

    public static final String allModifiers = "public protected private abstract static final transient volatile synchronized native strictfp transitive default ";

    @Test
    public void topClass() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(allModifiers + "class X{}"));
        assertProblems(result,
                "(line 1,col 1) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 1) Can have only one of 'final', 'abstract'.",
                "(line 1,col 1) 'transient' is not allowed here.",
                "(line 1,col 1) 'default' is not allowed here.",
                "(line 1,col 1) 'volatile' is not allowed here.",
                "(line 1,col 1) 'strictfp' is not allowed here.",
                "(line 1,col 1) 'private' is not allowed here.",
                "(line 1,col 1) 'protected' is not allowed here.",
                "(line 1,col 1) 'synchronized' is not allowed here.",
                "(line 1,col 1) 'native' is not allowed here.",
                "(line 1,col 1) 'transitive' is not allowed here.",
                "(line 1,col 1) 'static' is not allowed here."
        );
    }

    @Test
    public void nestedClass() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "class I{}}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) 'transient' is not allowed here.",
                "(line 1,col 9) 'default' is not allowed here.",
                "(line 1,col 9) 'strictfp' is not allowed here.",
                "(line 1,col 9) 'volatile' is not allowed here.",
                "(line 1,col 9) 'synchronized' is not allowed here.",
                "(line 1,col 9) 'native' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void localClass() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{ void x() {" + allModifiers + "class I{}}}"));
        assertProblems(result,
                "(line 1,col 20) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 20) Can have only one of 'final', 'abstract'.",
                "(line 1,col 20) 'transient' is not allowed here.",
                "(line 1,col 20) 'volatile' is not allowed here.",
                "(line 1,col 20) 'default' is not allowed here.",
                "(line 1,col 20) 'synchronized' is not allowed here.",
                "(line 1,col 20) 'native' is not allowed here.",
                "(line 1,col 20) 'transitive' is not allowed here.",
                "(line 1,col 20) 'strictfp' is not allowed here.",
                "(line 1,col 20) 'static' is not allowed here.",
                "(line 1,col 20) 'public' is not allowed here.",
                "(line 1,col 20) 'private' is not allowed here.",
                "(line 1,col 20) 'protected' is not allowed here."
        );
    }

    @Test
    public void topInterface() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(allModifiers + "interface X{}"));
        assertProblems(result,
                "(line 1,col 1) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 1) Can have only one of 'final', 'abstract'.",
                "(line 1,col 1) 'transient' is not allowed here.",
                "(line 1,col 1) 'volatile' is not allowed here.",
                "(line 1,col 1) 'default' is not allowed here.",
                "(line 1,col 1) 'strictfp' is not allowed here.",
                "(line 1,col 1) 'synchronized' is not allowed here.",
                "(line 1,col 1) 'native' is not allowed here.",
                "(line 1,col 1) 'transitive' is not allowed here.",
                "(line 1,col 1) 'static' is not allowed here.",
                "(line 1,col 1) 'final' is not allowed here.",
                "(line 1,col 1) 'private' is not allowed here.",
                "(line 1,col 1) 'protected' is not allowed here."
        );
    }

    @Test
    public void nestedInterface() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "interface I{}}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) 'transient' is not allowed here.",
                "(line 1,col 9) 'volatile' is not allowed here.",
                "(line 1,col 9) 'default' is not allowed here.",
                "(line 1,col 9) 'final' is not allowed here.",
                "(line 1,col 9) 'strictfp' is not allowed here.",
                "(line 1,col 9) 'synchronized' is not allowed here.",
                "(line 1,col 9) 'native' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void constructor() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "X(){};}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) 'transient' is not allowed here.",
                "(line 1,col 9) 'volatile' is not allowed here.",
                "(line 1,col 9) 'final' is not allowed here.",
                "(line 1,col 9) 'strictfp' is not allowed here.",
                "(line 1,col 9) 'synchronized' is not allowed here.",
                "(line 1,col 9) 'default' is not allowed here.",
                "(line 1,col 9) 'native' is not allowed here.",
                "(line 1,col 9) 'strictfp' is not allowed here.",
                "(line 1,col 9) 'abstract' is not allowed here.",
                "(line 1,col 9) 'static' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void constructorParameter() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{X(" + allModifiers + " int i){};}"));
        assertProblems(result,
                "(line 1,col 11) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 11) Can have only one of 'final', 'abstract'.",
                "(line 1,col 11) 'transient' is not allowed here.",
                "(line 1,col 11) 'volatile' is not allowed here.",
                "(line 1,col 11) 'synchronized' is not allowed here.",
                "(line 1,col 11) 'native' is not allowed here.",
                "(line 1,col 11) 'strictfp' is not allowed here.",
                "(line 1,col 11) 'default' is not allowed here.",
                "(line 1,col 11) 'abstract' is not allowed here.",
                "(line 1,col 11) 'static' is not allowed here.",
                "(line 1,col 11) 'transitive' is not allowed here.",
                "(line 1,col 11) 'private' is not allowed here.",
                "(line 1,col 11) 'public' is not allowed here.",
                "(line 1,col 11) 'protected' is not allowed here."
        );
    }

    @Test
    public void classMethod() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "int x(){};}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) Cannot be 'abstract' and also 'private', 'static', 'final', 'native', 'strictfp', 'synchronized'.",
                "(line 1,col 9) 'transient' is not allowed here.",
                "(line 1,col 9) 'default' is not allowed here.",
                "(line 1,col 9) 'strictfp' is not allowed here.",
                "(line 1,col 9) 'volatile' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void interfaceMethod() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X{" + allModifiers + "int x(){};}"));
        assertProblems(result,
                "(line 1,col 13) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 13) Can have only one of 'final', 'abstract'.",
                "(line 1,col 13) Cannot be 'abstract' and also 'private', 'static', 'final', 'native', 'strictfp', 'synchronized'.",
                "(line 1,col 13) 'transient' is not allowed here.",
                "(line 1,col 13) 'strictfp' is not allowed here.",
                "(line 1,col 13) 'volatile' is not allowed here.",
                "(line 1,col 13) 'default' is not allowed here.",
                "(line 1,col 13) 'transitive' is not allowed here.",
                "(line 1,col 13) 'private' is not allowed here.",
                "(line 1,col 13) 'static' is not allowed here."
        );
    }

    @Test
    public void methodParameter() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{int x(" + allModifiers + " int i){};}"));
        assertProblems(result,
                "(line 1,col 15) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 15) Can have only one of 'final', 'abstract'.",
                "(line 1,col 15) 'transient' is not allowed here.",
                "(line 1,col 15) 'volatile' is not allowed here.",
                "(line 1,col 15) 'synchronized' is not allowed here.",
                "(line 1,col 15) 'native' is not allowed here.",
                "(line 1,col 15) 'strictfp' is not allowed here.",
                "(line 1,col 15) 'abstract' is not allowed here.",
                "(line 1,col 15) 'default' is not allowed here.",
                "(line 1,col 15) 'static' is not allowed here.",
                "(line 1,col 15) 'transitive' is not allowed here.",
                "(line 1,col 15) 'private' is not allowed here.",
                "(line 1,col 15) 'public' is not allowed here.",
                "(line 1,col 15) 'protected' is not allowed here."
        );
    }

    @Test
    public void field() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "int i;}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) 'synchronized' is not allowed here.",
                "(line 1,col 9) 'native' is not allowed here.",
                "(line 1,col 9) 'strictfp' is not allowed here.",
                "(line 1,col 9) 'default' is not allowed here.",
                "(line 1,col 9) 'abstract' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void localVariable() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{int x(){" + allModifiers + "int i;}}"));
        assertProblems(result,
                "(line 1,col 17) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 17) Can have only one of 'final', 'abstract'.",
                "(line 1,col 17) 'transient' is not allowed here.",
                "(line 1,col 17) 'volatile' is not allowed here.",
                "(line 1,col 17) 'synchronized' is not allowed here.",
                "(line 1,col 17) 'native' is not allowed here.",
                "(line 1,col 17) 'default' is not allowed here.",
                "(line 1,col 17) 'strictfp' is not allowed here.",
                "(line 1,col 17) 'abstract' is not allowed here.",
                "(line 1,col 17) 'static' is not allowed here.",
                "(line 1,col 17) 'transitive' is not allowed here.",
                "(line 1,col 17) 'private' is not allowed here.",
                "(line 1,col 17) 'public' is not allowed here.",
                "(line 1,col 17) 'protected' is not allowed here."
        );
    }


    @Test
    public void catchParameter() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{int x(){ try{}catch(" + allModifiers + " Integer x){}}}"));
        assertProblems(result,
                "(line 1,col 144) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 144) Can have only one of 'final', 'abstract'.",
                "(line 1,col 144) 'transient' is not allowed here.",
                "(line 1,col 144) 'volatile' is not allowed here.",
                "(line 1,col 144) 'synchronized' is not allowed here.",
                "(line 1,col 144) 'native' is not allowed here.",
                "(line 1,col 144) 'default' is not allowed here.",
                "(line 1,col 144) 'strictfp' is not allowed here.",
                "(line 1,col 144) 'abstract' is not allowed here.",
                "(line 1,col 144) 'static' is not allowed here.",
                "(line 1,col 144) 'transitive' is not allowed here.",
                "(line 1,col 144) 'private' is not allowed here.",
                "(line 1,col 144) 'public' is not allowed here.",
                "(line 1,col 144) 'protected' is not allowed here."
        );
    }

    @Test
    public void innerClasses() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{class Y{}}"));
        assertNoProblems(result);
    }

    @Test
    public void localInterface() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{ void x() {" + allModifiers + "interface I{}}}"));
        assertProblems(result, "(line 1,col 20) There is no such thing as a local interface."
        );
    }

    @Test
    public void reflection() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("Abc.class"));
        assertNoProblems(result);
    }

    @Test
    public void strictfpAllowedAsIdentifier() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int strictfp;"));
        assertNoProblems(result);
    }
}
