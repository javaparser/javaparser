package com.github.jmlparser.smt;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver;
import com.github.jmlparser.smt.model.SExpr;
import com.google.common.truth.Truth;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;
import org.yaml.snakeyaml.Yaml;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.fail;

/**
 * @author Alexander Weigl
 * @version 1 (14.06.22)
 */
public class SmtTest {
    private final JavaParser parser;
    private final Node parent;

    {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ClassLoaderTypeSolver(ClassLoader.getSystemClassLoader())));
        parser = new JavaParser(config);

        ParseResult<CompilationUnit> r = parser.parse(getClass().getResourceAsStream("Test.java"));
        if (!r.isSuccessful()) {
            r.getProblems().forEach(System.err::println);
            fail("Error during parsing");
        }
        parent = r.getResult().get().getType(0);
    }

    @TestFactory
    public Stream<DynamicTest> smtTranslation() throws IOException {
        try (InputStream inputStream = getClass().getResourceAsStream("expr.yaml")) {
            Yaml yaml = new Yaml();
            List<Map<String, Object>> obj = yaml.load(inputStream);
            return obj.stream().map(m -> {
                String a = (String) m.get("expr");
                String result = (String) m.get("result");
                String resultInt = (String) m.get("resultInt");
                String resultBv = (String) m.get("resultBv");
                return DynamicTest.dynamicTest(a, () -> {
                    if (resultInt != null)
                        smtTranslation(a, resultInt, true);
                    if (resultBv != null)
                        smtTranslation(a, resultBv, false);
                    if (result != null)
                        smtTranslation(a, result, false);
                });
            });
        }
    }

    void smtTranslation(String input, String expected, boolean useInt) {
        ParseResult<Expression> e = parser.parseJmlExpression(input);
        if (!e.isSuccessful()) {
            e.getProblems().forEach(System.err::println);
            fail("Error during parsing");
        }
        Expression expr = e.getResult().get();
        expr.setParentNode(parent);
        SmtQuery smtLog = new SmtQuery();
        SExpr actualExpr = SMTFacade.toSmt(expr, smtLog, useInt);

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        smtLog.appendTo(pw);
        actualExpr.appendTo(pw);
        String actual = sw.toString();
        Truth.assertThat(actual.trim()).isEqualTo(expected.trim());
    }

}
