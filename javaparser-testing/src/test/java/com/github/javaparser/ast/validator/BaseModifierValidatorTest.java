package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class BaseModifierValidatorTest {
    private final String allModifiers = "public protected private abstract static final transient volatile synchronized native strictfp transitive ";

    @Test
    public void topClass() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider(allModifiers + "class X{}"));
        assertProblems(result,
                "(line 1,col 1) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 1) Can have only one of 'final', 'abstract'.",
                "(line 1,col 1) 'transient' is not allowed here.",
                "(line 1,col 1) 'volatile' is not allowed here.",
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
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "class I{}}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) 'transient' is not allowed here.",
                "(line 1,col 9) 'volatile' is not allowed here.",
                "(line 1,col 9) 'synchronized' is not allowed here.",
                "(line 1,col 9) 'native' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void localClass() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X{ void x() {" + allModifiers + "class I{}}}"));
        assertProblems(result,
                "(line 1,col 20) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 20) Can have only one of 'final', 'abstract'.",
                "(line 1,col 20) 'transient' is not allowed here.",
                "(line 1,col 20) 'volatile' is not allowed here.",
                "(line 1,col 20) 'synchronized' is not allowed here.",
                "(line 1,col 20) 'native' is not allowed here.",
                "(line 1,col 20) 'transitive' is not allowed here.",
                "(line 1,col 20) 'static' is not allowed here.",
                "(line 1,col 20) 'public' is not allowed here.",
                "(line 1,col 20) 'private' is not allowed here.",
                "(line 1,col 20) 'protected' is not allowed here."
        );
    }

    @Test
    public void topInterface() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider(allModifiers + "interface X{}"));
        assertProblems(result,
                "(line 1,col 1) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 1) Can have only one of 'final', 'abstract'.",
                "(line 1,col 1) 'transient' is not allowed here.",
                "(line 1,col 1) 'volatile' is not allowed here.",
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
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "interface I{}}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) 'transient' is not allowed here.",
                "(line 1,col 9) 'volatile' is not allowed here.",
                "(line 1,col 9) 'final' is not allowed here.",
                "(line 1,col 9) 'synchronized' is not allowed here.",
                "(line 1,col 9) 'native' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void localInterface() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X{ void x() {" + allModifiers + "interface I{}}}"));
        assertProblems(result,
                "(line 1,col 20) There is no such thing as a local interface."
        );
    }

    @Test
    public void topEnum() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider(allModifiers + "enum X{}"));
        assertProblems(result,
                "(line 1,col 1) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 1) Can have only one of 'final', 'abstract'.",
                "(line 1,col 1) 'transient' is not allowed here.",
                "(line 1,col 1) 'volatile' is not allowed here.",
                "(line 1,col 1) 'synchronized' is not allowed here.",
                "(line 1,col 1) 'native' is not allowed here.",
                "(line 1,col 1) 'transitive' is not allowed here.",
                "(line 1,col 1) 'static' is not allowed here.",
                "(line 1,col 1) 'abstract' is not allowed here.",
                "(line 1,col 1) 'final' is not allowed here.",
                "(line 1,col 1) 'private' is not allowed here.",
                "(line 1,col 1) 'protected' is not allowed here."
        );
    }

    @Test
    public void nestedEnum() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "enum I{}}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) 'transient' is not allowed here.",
                "(line 1,col 9) 'volatile' is not allowed here.",
                "(line 1,col 9) 'abstract' is not allowed here.",
                "(line 1,col 9) 'final' is not allowed here.",
                "(line 1,col 9) 'synchronized' is not allowed here.",
                "(line 1,col 9) 'native' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void topAnnotationDeclaration() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider(allModifiers + "@interface X{}"));
        assertProblems(result,
                "(line 1,col 1) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 1) Can have only one of 'final', 'abstract'.",
                "(line 1,col 1) 'transient' is not allowed here.",
                "(line 1,col 1) 'volatile' is not allowed here.",
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
    public void nestedAnnotationDeclaration() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X{" + allModifiers + "@interface I{}}"));
        assertProblems(result,
                "(line 1,col 9) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 9) Can have only one of 'final', 'abstract'.",
                "(line 1,col 9) 'transient' is not allowed here.",
                "(line 1,col 9) 'volatile' is not allowed here.",
                "(line 1,col 9) 'final' is not allowed here.",
                "(line 1,col 9) 'synchronized' is not allowed here.",
                "(line 1,col 9) 'native' is not allowed here.",
                "(line 1,col 9) 'transitive' is not allowed here."
        );
    }

    @Test
    public void annotationMember() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("@interface X{" + allModifiers + "int x();}"));
        assertProblems(result,
                "(line 1,col 14) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 14) Can have only one of 'final', 'abstract'.",
                "(line 1,col 14) 'transient' is not allowed here.",
                "(line 1,col 14) 'volatile' is not allowed here.",
                "(line 1,col 14) 'final' is not allowed here.",
                "(line 1,col 14) 'synchronized' is not allowed here.",
                "(line 1,col 14) 'native' is not allowed here.",
                "(line 1,col 14) 'protected' is not allowed here.",
                "(line 1,col 14) 'private' is not allowed here.",
                "(line 1,col 14) 'strictfp' is not allowed here.",
                "(line 1,col 14) 'static' is not allowed here.",
                "(line 1,col 14) 'transitive' is not allowed here."
        );
    }

    @Test
    public void moduleRequires() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("module x{requires " + allModifiers + " a;\n}"));
        assertProblems(result,
                "(line 1,col 10) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 10) Can have only one of 'final', 'abstract'.",
                "(line 1,col 10) 'transient' is not allowed here.",
                "(line 1,col 10) 'volatile' is not allowed here.",
                "(line 1,col 10) 'final' is not allowed here.",
                "(line 1,col 10) 'synchronized' is not allowed here.",
                "(line 1,col 10) 'native' is not allowed here.",
                "(line 1,col 10) 'private' is not allowed here.",
                "(line 1,col 10) 'protected' is not allowed here.",
                "(line 1,col 10) 'strictfp' is not allowed here.",
                "(line 1,col 10) 'abstract' is not allowed here.",
                "(line 1,col 10) 'public' is not allowed here."
        );
    }

}
