package io.github.jmltoolkit.jml2java

import io.github.jmltoolkit.utils.Pattern
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (11.10.22)
 */
internal class PatternTest {
    @Test
    fun matchIf() {
        val cond = com.github.javaparser.ast.expr.NameExpr("_")
        val then = com.github.javaparser.ast.stmt.ExpressionStmt()
        val other = com.github.javaparser.ast.stmt.ExpressionStmt()
        val ifPattern = Pattern(com.github.javaparser.ast.stmt.IfStmt(cond, then, other))
        ifPattern.addPlaceholder(cond, "c")
        ifPattern.addPlaceholder(then, "t")
        ifPattern.addPlaceholder(other, "o")

        val candidate = com.github.javaparser.StaticJavaParser.parseStatement("if(a<b+1) print(a); else print(b);")
        val result1 = ifPattern.match(candidate)
        println(result1)
    }
}