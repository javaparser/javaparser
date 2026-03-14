package io.github.jmltoolkit.redux


import com.github.javaparser.ast.Node

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
interface Transformer {
    fun apply(a: Node): Node
}
