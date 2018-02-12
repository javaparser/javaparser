package com.github.javaparser.ast.type;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.validator.Java5Validator;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseType;
import static com.github.javaparser.JavaParser.parseVariableDeclarationExpr;
import static com.github.javaparser.ParseStart.VARIABLE_DECLARATION_EXPR;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.*;

public class TypeTest {
    @Test
    public void asString() {
        assertEquals("int", typeAsString("int x"));
        assertEquals("List<Long>", typeAsString("List<Long> x"));
        assertEquals("String", typeAsString("@A String x"));
        assertEquals("List<? extends Object>", typeAsString("List<? extends Object> x"));
    }

    @Test(expected = ParseProblemException.class)
    public void primitiveTypeArgumentDefaultValidator() {
        typeAsString("List<long> x;");
    }

    @Test
    public void primitiveTypeArgumentLenientValidator() {
        ParserConfiguration config = new ParserConfiguration()
                .setLanguageLevel(RAW);
        config.getPostProcessors().add(new Java5Validator() {{
            remove(noPrimitiveGenericArguments);
        }}.postProcessor());

        ParseResult<VariableDeclarationExpr> result = new JavaParser(config).parse(
                VARIABLE_DECLARATION_EXPR, provider("List<long> x"));
        assertTrue(result.isSuccessful());

        VariableDeclarationExpr decl = result.getResult().get();
        assertEquals("List<long>", decl.getVariable(0).getType().asString());
    }

    private String typeAsString(String s) {
        return parseVariableDeclarationExpr(s).getVariable(0).getType().asString();
    }

    @Test
    public void arrayType() {
        Type type = parseType("int[]");
        assertTrue(type.isArrayType());
        ArrayType arrayType = type.asArrayType();
        final ArrayType[] s = new ArrayType[1];
        type.ifArrayType(t -> s[0] = t);
        assertNotNull(s[0]);
    }

    @Test
    public void issue1251() {
        final Type type = parseType("TypeUtilsTest<String>.Tester");
        assertEquals("TypeUtilsTest<String>.Tester", type.toString());
    }

}
