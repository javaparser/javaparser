package io.github.jmltoolkit.lsp.actions

import com.github.javaparser.ast.expr.Expression
import io.github.jmltoolkit.lsp.JmlLanguageServer
import io.github.jmltoolkit.lsp.asRange
import org.eclipse.lsp4j.*
import java.util.concurrent.CompletableFuture

object WellDefinednessCheck : LspAction<Expression> {
    override val id: String
        get() = "jml.welldefinedness-check"
    override val title: String
        get() = "Check expression for well-definedness"

    override fun execute(server: JmlLanguageServer, value: List<Any>): CompletableFuture<Any> {
        println("WellDefinednessCheck.execute server = [${server}], value = [${value}]")
        return CompletableFuture.completedFuture(null)
    }

    fun createCommand(node: Expression): Command = command(listOf(node.hashCode()))

    override fun createCodeLens(node: Expression): CodeLens = TODO() // CodeLens(node.asRange, command(), null)
    fun createCodeAction(n: Expression): CodeAction =
        CodeAction(title).also {
            it.command = command()
            it.kind = CodeActionKind.QuickFix
        }
}

//    val ca = Command("WD-check", "jml.welldefinedCheck", listOf(r))