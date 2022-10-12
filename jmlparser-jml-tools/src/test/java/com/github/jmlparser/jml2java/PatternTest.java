package com.github.jmlparser.jml2java;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.jmlparser.utils.Pattern;
import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (11.10.22)
 */
class PatternTest {

    @Test
    void matchIf() {
        final var cond = new NameExpr("_");
        final var then = new ExpressionStmt();
        final var other = new ExpressionStmt();
        final var ifPattern = new Pattern<>(new IfStmt(cond, then, other));
        ifPattern.addPlaceholder(cond, "c");
        ifPattern.addPlaceholder(then, "t");
        ifPattern.addPlaceholder(other, "o");

        var candidate = StaticJavaParser.parseStatement("if(a<b+1) print(a); else print(b);");
        var result1 = ifPattern.match(candidate);
        System.out.println(result1);
    }
}