package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class ParserConfigurationTest {
    @Test
    public void storeNoTokens() {
        ParseResult<CompilationUnit> result = new JavaParser(new ParserConfiguration().setStoreTokens(false)).parse(ParseStart.COMPILATION_UNIT, provider("class X{}"));
        
        assertEquals(false, result.getTokens().isPresent());
        assertEquals(true, result.getResult().get().getChildNodesByType(Node.class).stream().noneMatch(node -> node.getTokenRange().isPresent()));
    }
}
