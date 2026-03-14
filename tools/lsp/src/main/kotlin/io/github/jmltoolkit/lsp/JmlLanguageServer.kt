package io.github.jmltoolkit.lsp

import io.github.jmltoolkit.lsp.actions.LspAction
import io.github.jmltoolkit.lsp.highlighting.LEGEND
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.services.*
import java.util.*
import java.util.concurrent.CompletableFuture
import java.util.concurrent.ExecutorService
import java.util.concurrent.ForkJoinPool
import kotlin.system.exitProcess


class JmlLanguageServer : LanguageServer, LanguageClientAware {
    internal val executorService: ExecutorService = ForkJoinPool.commonPool()
    internal val jmlTextDocumentService by lazy { JmlTextDocumentService(this) }
    internal val jmlWorkspaceService by lazy { JmlWorkspaceService(this) }

    internal lateinit var client: LanguageClient
    internal var capabilities: ClientCapabilities? = null
    internal lateinit var workspaceFolders: List<WorkspaceFolder>
    internal val jmlNotebookDocumentServices by lazy { JmlNotebookDocumentServices() }

    internal val config = ProjectDefinitionService()

    internal val actions by lazy {
        ServiceLoader.load(LspAction::class.java).toList()
    }

    override fun initialize(params: InitializeParams): CompletableFuture<InitializeResult> {
        workspaceFolders = params.workspaceFolders
        capabilities = params.capabilities

        config.update(workspaceFolders.map { Uri(it.uri) })

        return CompletableFuture.supplyAsync {
            val capabilities = ServerCapabilities()
            capabilities.setTextDocumentSync(TextDocumentSyncKind.Full)
            capabilities.diagnosticProvider = DiagnosticRegistrationOptions(true, false)
            capabilities.setDocumentSymbolProvider(true)
            capabilities.setWorkspaceSymbolProvider(true)

            capabilities.setDeclarationProvider(DeclarationRegistrationOptions("JML"))

            // capabilities.signatureHelpProvider = SignatureHelpOptions()
            capabilities.setHoverProvider(true)

            // capabilities.codeLensProvider = CodeLensOptions(false)
            capabilities.setSelectionRangeProvider(true)

            //capabilities.setDefinitionProvider(true)
            //capabilities.setDocumentHighlightProvider(true)
            //capabilities.completionProvider = CompletionOptions(true, null)

            capabilities.semanticTokensProvider = SemanticTokensWithRegistrationOptions(
                LEGEND, SemanticTokensServerFull(false), false,
                listOf(
                    DocumentFilter("java", "file", "*.java"),
                    DocumentFilter("key", "file", "*.key"),
                )
            )

            // capabilities.setCodeActionProvider(CodeActionOptions(listOf("validity")))
            // capabilities.executeCommandProvider = ExecuteCommandOptions(actions.map { it.id })

            return@supplyAsync InitializeResult(capabilities)
        }
    }

    override fun shutdown(): CompletableFuture<Any> {
        executorService.shutdownNow()
        return CompletableFuture.completedFuture("finish")
    }

    override fun exit() {
        shutdown()
        exitProcess(0)
    }

    override fun getNotebookDocumentService(): NotebookDocumentService = jmlNotebookDocumentServices

    override fun getTextDocumentService(): TextDocumentService = jmlTextDocumentService

    override fun getWorkspaceService(): WorkspaceService = jmlWorkspaceService

    override fun connect(client: LanguageClient) {
        this.client = client
    }
}
