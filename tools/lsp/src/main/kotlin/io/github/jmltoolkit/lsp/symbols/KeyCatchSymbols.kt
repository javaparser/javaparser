package io.github.jmltoolkit.lsp.symbols

import de.uka.ilkd.key.nparser.KeYParser
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor
import de.uka.ilkd.key.nparser.ParsingFacade
import io.github.jmltoolkit.lsp.Uri
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token
import org.antlr.v4.runtime.tree.ParseTree
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.jsonrpc.messages.Either

private val Token.asRange: Range
    get() = Range(asStartPosition, asStopPosition)
private val Token.asStopPosition: Position
    get() = Position(line, charPositionInLine + startIndex - stopIndex)
private val Token.asStartPosition: Position
    get() = Position(line, charPositionInLine)
private val ParserRuleContext.asRange: Range
    get() = Range(start.asStartPosition, stop.asStopPosition)

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.02.24)
 */
class KeyCatchSymbols(private val uri: Uri) {
    fun run(): MutableList<Either<SymbolInformation, DocumentSymbol>> {
        val file = ParsingFacade.parseFile(uri.path)
        val ctx = ParsingFacade.getParseRuleContext(file)
        val v = Visitor()
        val l = ctx.accept(v)
        return l.map { Either.forRight<SymbolInformation, DocumentSymbol>(it) }.toMutableList()
    }

    private class Visitor : KeYParserBaseVisitor<List<DocumentSymbol>>() {
        override fun visitFile(ctx: KeYParser.FileContext): List<DocumentSymbol> = acceptAll(ctx.children)
        @JvmName("acceptAllPt")
        private fun acceptAll(children: List<ParseTree>): List<DocumentSymbol> =
            children.mapNotNull { it as? ParserRuleContext }
                .flatMap { it.accept(this) }.toMutableList()

        private fun acceptAll(children: List<ParserRuleContext>): MutableList<DocumentSymbol> =
            children.flatMap { it.accept(this) }.toMutableList()

        override fun visitDecls(ctx: KeYParser.DeclsContext): List<DocumentSymbol> = acceptAll(ctx.children)

        override fun visitSort_decls(ctx: KeYParser.Sort_declsContext) = listOf(
            DocumentSymbol(
                "Sorts", SymbolKind.Namespace, ctx.asRange,
                Range(),
                null,
                acceptAll(ctx.one_sort_decl())
            )
        )

        override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext): List<DocumentSymbol> =
            ctx.sortIds.simple_ident_dots().flatMap {
                symbol(it.text, SymbolKind.Class, it.asRange, it.asRange, ctx.doc?.text)
            }

        private fun symbol(
            name: String,
            kind: SymbolKind,
            range: Range,
            selectionRange: Range,
            detail: String? = null,
            children: MutableList<DocumentSymbol>? = null
        ): List<DocumentSymbol> = listOf(
            DocumentSymbol(name, kind, range, selectionRange, detail, children)
        )


        override fun visitPreferences(ctx: KeYParser.PreferencesContext): List<DocumentSymbol> =
            symbol("Preferences", SymbolKind.String, ctx.KEYSETTINGS().symbol.asRange, ctx.asRange, ctx.text)


        override fun visitFunc_decls(ctx: KeYParser.Func_declsContext) = symbol(
            "Functions", SymbolKind.Function,
            ctx.start.asRange, Range(), null,
            acceptAll(ctx.func_decl())
        )

        override fun visitRulesOrAxioms(ctx: KeYParser.RulesOrAxiomsContext) = symbol(
            (if (ctx.RULES() != null) "Rules" else "Axioms") + " ${ctx.choices.text}",
            SymbolKind.Namespace, ctx.start.asRange, ctx.asRange, ctx.doc?.text,
            acceptAll(ctx.taclet())
        )
    }
}