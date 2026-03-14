package io.github.jmltoolkit.lsp

import org.eclipse.lsp4j.DidChangeNotebookDocumentParams
import org.eclipse.lsp4j.DidCloseNotebookDocumentParams
import org.eclipse.lsp4j.DidOpenNotebookDocumentParams
import org.eclipse.lsp4j.DidSaveNotebookDocumentParams
import org.eclipse.lsp4j.services.NotebookDocumentService

class JmlNotebookDocumentServices : NotebookDocumentService {
    override fun didOpen(params: DidOpenNotebookDocumentParams?) {}

    override fun didChange(params: DidChangeNotebookDocumentParams?) {}

    override fun didSave(params: DidSaveNotebookDocumentParams?) {}

    override fun didClose(params: DidCloseNotebookDocumentParams?) {}

}
