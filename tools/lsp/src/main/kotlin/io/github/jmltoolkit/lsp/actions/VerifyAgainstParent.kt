package io.github.jmltoolkit.lsp.actions

import com.github.javaparser.ast.jml.clauses.JmlContract
import com.google.common.cache.CacheBuilder
import io.github.jmltoolkit.lsp.JmlLanguageServer
import io.github.jmltoolkit.lsp.asRange
import org.eclipse.lsp4j.CodeLens
import org.eclipse.lsp4j.MessageParams
import org.eclipse.lsp4j.MessageType
import java.util.concurrent.CompletableFuture

object VerifyAgainstParent : LspAction<JmlContract> {
    override val id: String = "jml.verify.liskov"
    override val title: String = "Verify against parent"

    private val cache = CacheBuilder.newBuilder().softValues().build<Int, JmlContract>()

    override fun execute(server: JmlLanguageServer, value: List<Any>): CompletableFuture<Any> {
        cache.getIfPresent(value.first())?.let {
            server.client.showMessage(
                MessageParams(MessageType.Warning, "Prove is not implemented yet.")
            )
        }
        return CompletableFuture.completedFuture("")
    }

    override fun createCodeLens(node: JmlContract): CodeLens {
        cache.put(node.hashCode(), node)
        return CodeLens(node.asRange, command(listOf(node.hashCode())), null)
    }
}