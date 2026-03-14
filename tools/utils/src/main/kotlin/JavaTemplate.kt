package io.github.jmltoolkit.utils

import com.github.javaparser.StaticJavaParser
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.body.BodyDeclaration
import com.github.javaparser.ast.body.TypeDeclaration
import com.github.javaparser.ast.expr.SimpleName
import com.github.javaparser.ast.stmt.BlockStmt
import com.github.javaparser.ast.stmt.Statement

/**
 * @author Alexander Weigl
 * @version 1 (10.10.22)
 */
class JavaTemplate<T : Node>(private val template: T) {
    fun instantiate(substitutionFactory: SubstitutionFactory): T {
        val copy = template.clone()
        replace<Node, Node>(copy, substitutionFactory)
        return copy as T
    }

    private fun <R : Node?, O : Node?> replace(node: Node, factory: SubstitutionFactory) {
        for (childNode in node.childNodes) {
            replace<Node, Node>(childNode, factory)
            if (factory.replacable(childNode)) {
                node.replace(childNode, factory.substitutionOf(childNode))
            }
        }
    }

    interface SubstitutionFactory {
        fun replacable(node: Node): Boolean

        fun substitutionOf(node: Node): Node
    }

    class IdentifierSubstitution @JvmOverloads constructor(private val map: MutableMap<String?, String?> = HashMap()) :
        SubstitutionFactory {
        fun add(name: String?, newName: String?) {
            map[name] = newName
        }

        override fun replacable(node: Node): Boolean {
            return node is SimpleName && map.containsKey(node.asString())
        }

        override fun substitutionOf(node: Node): Node {
            if (node is SimpleName) node.setIdentifier(map[node.asString()])
            return node
        }
    }

    companion object {
        fun fromBlock(javaCode: String?): JavaTemplate<BlockStmt> {
            return JavaTemplate(StaticJavaParser.parseBlock(javaCode))
        }

        fun fromStatement(javaCode: String?): JavaTemplate<Statement> {
            return JavaTemplate(StaticJavaParser.parseStatement(javaCode))
        }

        fun fromType(javaCode: String?): JavaTemplate<TypeDeclaration<*>> {
            return JavaTemplate(StaticJavaParser.parseTypeDeclaration(javaCode))
        }

        fun fromBodyDecl(javaCode: String?): JavaTemplate<BodyDeclaration<*>> {
            return JavaTemplate(StaticJavaParser.parseBodyDeclaration(javaCode))
        }
    }
}
