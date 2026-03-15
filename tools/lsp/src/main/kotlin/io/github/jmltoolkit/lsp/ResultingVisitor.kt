package io.github.jmltoolkit.lsp

import com.github.javaparser.ast.visitor.VoidVisitorAdapter

/**
 * Defines a visitor which produces a result of type `T`.
 * @author Alexander Weigl
 * @version 1 (20.07.22)
 */
abstract class ResultingVisitor<T> : VoidVisitorAdapter<Unit?>() {
    abstract val result: T
}