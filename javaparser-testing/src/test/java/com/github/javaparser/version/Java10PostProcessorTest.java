package com.github.javaparser.version;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.VarType;
import org.junit.Test;

import java.util.List;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_10_PREVIEW;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class Java10PostProcessorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_10_PREVIEW));

    @Test
    public void varIsAType() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("var x=\"\";"));

        List<VarType> allVarTypes = result.getResult().get().findAll(VarType.class);

        assertEquals(1, allVarTypes.size());
    }

    @Test
    public void varAllowedInLocalVariableDeclaration() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("var a = 5;"));
        assertNoProblems(result);
    }

    @Test
    public void varAllowedInForEach() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for(var a : as){}"));
        assertNoProblems(result);
    }

    @Test
    public void varAllowedInOldFor() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for(var a = 5;a<9;a++){}"));
        assertNoProblems(result);
    }
}
