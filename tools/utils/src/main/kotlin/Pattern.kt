package io.github.jmltoolkit.utils

import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (11.10.22)
 */
class Pattern<T : Node?>(private val pattern: T) {
    private val placeholders: MutableMap<Node, String> = IdentityHashMap()
    fun match(tree: Node?): Map<String, Node>? {
        return match(pattern, tree, HashMap<String, Node>())
    }

    private fun match(pattern: Node?, tree: Node?, map: MutableMap<String, Node>): MutableMap<String, Node>? {
        if (pattern == null && tree == null)
            return map

        if ((pattern != null) xor (tree != null))
            return null

        require(pattern != null)
        require(tree != null)

        var rmap: MutableMap<String, Node>? = map

        if (placeholders.containsKey(pattern)) {
            val key = placeholders[pattern]
            if (map.containsKey(key) && map[key] != tree) return null
            else {
                map[key!!] = tree
            }
            return map
        }

        if (pattern.javaClass !== tree.javaClass) return null


        for (prop in pattern.metaModel.allPropertyMetaModels) {
            val childPattern = prop.getValue(pattern)
            val childTree = prop.getValue(tree)

            if (prop.isNode) {
                rmap = match(childPattern as Node?, childTree as Node?, map)
                if (rmap == null)
                    return null
            } else if (prop.isNodeList) {
                val a = childPattern as NodeList<out Node?>
                val b = childTree as NodeList<out Node?>
                if (a.size != b.size) return null

                for (i in 0 until a.size) {
                    rmap = match(a[i], b[i], map)
                    if (rmap == null)
                        return null
                }
            } else {
                if (!childPattern.equals(childTree)) return null
            }
        }

        return rmap
    }


    fun find(n: Node): Map<String, Node>? {
        val queue: ArrayDeque<Node> = ArrayDeque<Node>()
        queue.add(n)
        while (!queue.isEmpty()) {
            val e: Node = queue.pop()
            val r = match(e)
            if (r != null)
                return r
            queue.addAll(e.childNodes)
        }
        return null
    }

    fun addPlaceholder(placeholder: Node, label: String) {
        placeholders[placeholder] = label
    }
}
