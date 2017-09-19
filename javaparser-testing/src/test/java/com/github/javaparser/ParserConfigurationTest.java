package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.assertFalse;

public class ParserConfigurationTest {
    @Test
    public void storeNoTokens() {
        ParseResult<CompilationUnit> result = new JavaParser(new ParserConfiguration().setStoreTokens(false)).parse(ParseStart.COMPILATION_UNIT, provider("class X{}"));
        
        assertFalse(result.getTokens().isPresent());
        assertFalse(result.getResult().get().getTokenRange().isPresent());
    }
}
