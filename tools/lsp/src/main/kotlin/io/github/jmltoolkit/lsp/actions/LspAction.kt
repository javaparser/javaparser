package io.github.jmltoolkit.lsp.actions

import com.github.javaparser.ast.Node
import io.github.jmltoolkit.lsp.JmlLanguageServer
import org.eclipse.lsp4j.CodeLens
import org.eclipse.lsp4j.Command
import java.util.concurrent.CompletableFuture

/**
 * This class encapsulates both the execution of an action on the ast, and the metadata.
 * @author Alexander Weigl
 * @version 1 (16.10.22)
 */
interface LspAction<T : Node> {
    val id: String
    val title: String

    fun command(args: List<Any>? = null): Command = Command(title, id, args)

    fun execute(server: JmlLanguageServer, value: List<Any>): CompletableFuture<Any>

    fun createCodeLens(node: T): CodeLens
}
