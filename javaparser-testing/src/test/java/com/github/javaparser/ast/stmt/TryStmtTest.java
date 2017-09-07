package com.github.javaparser.ast.stmt;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.validator.Java9Validator;
import org.junit.Test;

import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.assertTrue;

public class TryStmtTest {
    @Test
    public void simpleTest() {
        parse9("try(Reader x = new FileReader()){}");
    }

    @Test
    public void multipleTest() {
        parse9("try(Reader x = new FileReader(); Reader x = new FileReader()){}");
    }

    @Test
    public void modifiersTest() {
        parse9("try(final @A Reader x = new FileReader()){}");
    }

    @Test
    public void simpleVariable() {
        parse9("try(a){}");
    }

    @Test
    public void twoSimpleVariables() {
        parse9("try(a;b){}");
    }

    @Test
    public void complexVariable() {
        parse9("try(a.b.c){}");
    }

    @Test
    public void superAccess() {
        parse9("try(super.a){}");
    }

    @Test
    public void outerClassAccess() {
        parse9("try(X.this.a){}");
    }

    private void parse9(String code) {
        JavaParser parser = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));
        ParseResult<Statement> result = parser.parse(ParseStart.STATEMENT, provider(code));
        assertTrue(result.toString(), result.isSuccessful());
    }
}
