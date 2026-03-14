package io.github.jmltoolkit.utils

import com.github.javaparser.ast.Jmlish
import com.github.javaparser.ast.Node
import java.util.*
import java.util.function.Function

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
object Helper {
    fun <T : Node?> findAndApply(clazz: Class<T>, node: Node, fn: Function<T, Node>): Node {
        if (clazz.isAssignableFrom(node.javaClass)) {
            return fn.apply(node as T)
        }

        val queue: Queue<Node> = ArrayDeque<Node>(1024)
        queue.add(node)

        while (!queue.isEmpty()) {
            val n: Node = queue.poll()
            if (clazz.isAssignableFrom(node.javaClass)) {
                val other: Node = fn.apply(n as T)
                if (other !== n) {
                    n.replace(n, other)
                }
            } else {
                //traverse
                queue.addAll(node.childNodes)
            }
        }

        return node
    }

    fun findAllJmlContainers(cu: Node): List<Node> {
        val queue: LinkedList<Node> = LinkedList<Node>()
        queue.add(cu)
        val res: MutableList<Node> = ArrayList<Node>(128)
        while (!queue.isEmpty()) {
            val n: Node = queue.pollLast()
            if (n is Jmlish) {
                res.add(n)
            } else {
                queue.addAll(n.childNodes)
            }
        }
        return res
    }
}
