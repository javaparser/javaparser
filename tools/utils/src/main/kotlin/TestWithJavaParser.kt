package io.github.jmltoolkit.utils

import com.github.javaparser.JavaParser
import com.github.javaparser.ParserConfiguration
import com.github.javaparser.Problem
import com.github.javaparser.ast.Node
import com.github.javaparser.symbolsolver.JavaSymbolSolver
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver
import java.util.function.Consumer

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
open class TestWithJavaParser {
    protected val parser: JavaParser
    protected var parent: Node? = null

    init {
        val config = ParserConfiguration()
        config.setProcessJml(true)
        config.setSymbolResolver(JavaSymbolSolver(ClassLoaderTypeSolver(ClassLoader.getSystemClassLoader())))
        parser = JavaParser(config)

        val resourceAsStream = javaClass.getResourceAsStream("Test.java")
        if (resourceAsStream != null) {
            val r = parser.parse(resourceAsStream)
            if (!r.isSuccessful) {
                r.problems.forEach(Consumer { x: Problem? -> System.err.println(x) })
                error("Error during parsing")
            }
            parent = r.result.get().getType(0)
        } else {
            parent = null
        }
    }
}
