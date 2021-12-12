package com.github.jml.printer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;
import org.junit.jupiter.params.provider.MethodSource;

import static com.github.javaparser.StaticJavaParser.parseJmlExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ConcreteSyntaxModelTest {

    private String print(Node node) {
        return ConcreteSyntaxModel.genericPrettyPrint(node);
    }

    @ParameterizedTest()
    @CsvFileSource(resources = "/csm_jml_expression.txt", delimiterString = "FOOBARFOOBAZ")
    void printQuantifiedExpr(String line) {
        Expression expr = parseJmlExpression(line);
        assertEquals(line, print(expr));
    }
}