import com.google.common.truth.Truth
import io.github.jmltoolkit.lsp.hover.JmlDocumentationIndex
import io.github.jmltoolkit.lsp.JmlLanguageServer
import io.github.jmltoolkit.lsp.Uri
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.services.LanguageClient
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestFactory
import java.io.File
import java.util.concurrent.CompletableFuture
import kotlin.test.assertTrue

private val File.toUri: String
    get() = "file://${absolutePath}"


val workspace = File("workspace")
val languageServer = JmlLanguageServer().also {
    val params = InitializeParams()
    val workspaceFolder = WorkspaceFolder(workspace.toUri, "Test Bed")
    params.workspaceFolders = arrayListOf(workspaceFolder)
    it.connect(EmptyLanguageClient())
    it.initialize(params).get()
}

val docService = languageServer.textDocumentService

class EmptyLanguageClient : LanguageClient {
    override fun telemetryEvent(`object`: Any?) {
    }

    override fun publishDiagnostics(diagnostics: PublishDiagnosticsParams?) {
    }

    override fun showMessage(messageParams: MessageParams?) {
    }

    override fun showMessageRequest(requestParams: ShowMessageRequestParams?): CompletableFuture<MessageActionItem> {
        return CompletableFuture.completedFuture(MessageActionItem("Test!"))
    }

    override fun logMessage(message: MessageParams?) {
    }
}

class HoverTest {

    @Test
    fun docIndex() {
        val idx = JmlDocumentationIndex()
        val mbtext = idx.get("model_behavior")
        val btext = idx.get("behavior")
        Truth.assertThat(mbtext).isEqualTo(btext)
    }

    @Test
    fun test1() {
        val file = TextDocumentIdentifier(File(workspace, "Example.java").toUri)
        val params = HoverParams(file, Position(12, 10)) // requires
        val resp = docService.hover(params).get()
        println(resp.range)
        println(resp.contents.right.value)
    }
}

class CodeActionTests {
    @Test
    fun test1() {
        val file = TextDocumentIdentifier(File(workspace, "Example.java").toUri)
        val params = CodeActionParams(
            file, Range(Position(6, 35), Position(6, 35)),
            CodeActionContext(listOf(), null)
        )
        val resp = docService.codeAction(params).get()
        println(resp)
        with(Truth.assertThat(resp)) {
            isNotNull()
            isNotEmpty()
        }
    }
}

class FileDiagnosticTests {
    @Test
    fun test1() {
        val file = TextDocumentIdentifier(File(workspace, "Errors.java").toUri)
        val params = DocumentDiagnosticParams(file)
        val resp = docService.diagnostic(params).get()
        resp.left.items.forEach {
            println(it.message)
        }
    }
}

class DeclarationTests {
    @Test
    fun test1() {
        val file = TextDocumentIdentifier(File(workspace, "Declarations.java").toUri)
        val variableInClause = DeclarationParams(file, Position(5, 16))
        val variableInAssert = DeclarationParams(file, Position(10, 18))
        val forall = DeclarationParams(file, Position(7, 16))

        val result0 = docService.declaration(forall).get()
        println(result0)

        //val result1 = docService.declaration(variableInClause).get()
        //val result2 = docService.declaration(variableInAssert).get()

    }
}

class HighlighterTest {
    data class Entry(
        val line: Int,
        val column: Int,
        val len: Int,
        val type: Int,
        val modifiers: Int
    ) {
        constructor(pos: Int, data: List<Int>) : this(
            data[pos],
            data[pos + 1],
            data[pos + 2],
            data[pos + 3],
            data[pos + 4]
        )
    }

    @Test
    fun test1() {
        val file = TextDocumentIdentifier(File(workspace, "Declarations.java").toUri)
        val res = docService.semanticTokensFull(SemanticTokensParams(file)).get()

        assertTrue { res.data.size % 5 == 0 }
        val entries = mutableListOf<Entry>()
        for (i in 0 until res.data.size / 5) {
            val entry = Entry(5 * i, res.data)
            assertTrue { entry.column >= 0 }
            assertTrue { entry.line >= 0 }
            assertTrue { entry.len >= 1 }
            assertTrue { entry.type >= 0 }
            entries.add(entry)
        }

        var line = -1
        var column = 0
        val text = Uri(file.uri).file.readText().split("\n")

        for (entry in entries) {
            line += entry.line
            if (entry.line != 0) column = entry.column
            else column += entry.column
            val image = text[line].substring(column - 1, column - 1 + entry.len)
            println(image)
        }


        /*
            at index 5*i - deltaLine: token line number, relative to the previous token
            at index 5*i+1 - deltaStart: token start character, relative to the previous token (relative to 0 or the previous
                token’s start if they are on the same line)
            at index 5*i+2 - length: the length of the token.
            at index 5*i+3 - tokenType: will be looked up in SemanticTokensLegend.tokenTypes. We currently ask that tokenType < 65536.
            at index 5*i+4 - tokenModifiers: each set bit will be looked up in SemanticTokensLegend.tokenModifiers
         */

    }
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.07.22)
 */
class DocumentSymbolTests {
    private fun testDocumentSymbols(javaFile: File, symbolsTruth: File) {
        val params = DocumentSymbolParams(TextDocumentIdentifier(javaFile.toUri))
        val result = docService.documentSymbol(params).get()
        val sb = toCsv(result.map { it.right }, javaFile.name)
        Truth.assertThat(sb.toString())
            .isEqualTo(symbolsTruth.readText())
    }

    @TestFactory
    fun documentSymbols(): List<DynamicTest> {
        println(workspace.absoluteFile)

        return workspace.absoluteFile.walkTopDown().asSequence()
            .filter {
                File("$it.symbols").exists()
            }
            .filter { it.name.endsWith(".java") }
            .map { file ->
                DynamicTest.dynamicTest(file.name) {
                    testDocumentSymbols(file, File("$file.symbols"))
                }
            }
            .toList()
    }

    private fun toCsv(
        result: List<DocumentSymbol>,
        file: String,
        sb: StringBuilder = StringBuilder(),
        depth: Int = 0,
    ): StringBuilder {
        for (right in result) {
            sb.append(">".repeat(depth))
                .append(" ")
                .append(right.name)
                .append("\t")
                .append(right.kind)
                .append("\t")
                .append(file)
                .append(":")
                .append(right.selectionRange.start.line + 1)
                .append(":")
                .append(right.selectionRange.start.character + 1)
                .append("\n")
            toCsv(right.children, file, sb, depth + 1)
        }
        return sb
    }
}