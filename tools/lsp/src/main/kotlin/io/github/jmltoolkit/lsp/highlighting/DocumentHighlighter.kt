package io.github.jmltoolkit.lsp.highlighting

import com.github.javaparser.Token
import org.eclipse.lsp4j.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.02.24)
 */

interface DocumentHighlighter {
    fun analyzeJmlToken(text: String): SemanticTokens
}

enum class SupportedTokenTypes(val kind: String) {
    COMMENT(SemanticTokenTypes.Comment),
    VARIABLE(SemanticTokenTypes.Variable),
    KEYWORD(SemanticTokenTypes.Keyword),
    STRING(SemanticTokenTypes.String),
    NUMBER(SemanticTokenTypes.Number),
    MODIFIER(SemanticTokenTypes.Modifier),
}

enum class SupportedTokenModifier(val kind: String) {
    DECLARATION(SemanticTokenModifiers.Declaration),
    DOCUMENTATION(SemanticTokenModifiers.Documentation),
    DEPRECATED(SemanticTokenModifiers.Deprecated),
    STATIC(SemanticTokenModifiers.Static),
}

private val Token.asRange: Range
    get() = Range(Position(beginLine, beginColumn), Position(endLine, endColumn))

val tokenTypes = SupportedTokenTypes.entries.map { it.kind }
val tokenModifiers = SupportedTokenModifier.entries.map { it.kind }
val LEGEND: SemanticTokensLegend = SemanticTokensLegend(tokenTypes, tokenModifiers)


/*
    There are different ways how the position of a token can be expressed in a file.
    Absolute positions or relative positions. The protocol for the token format relative uses
    relative positions, because most tokens remain stable relative to each other when edits
    are made in a file. This simplifies the computation of a delta if a server supports it.
    So each token is represented using 5 integers. A specific token i in the file consists
    of the following array indices:

    at index 5*i - deltaLine: token line number, relative to the previous token
    at index 5*i+1 - deltaStart: token start character, relative to the previous token (relative to 0 or the previous
    token’s start if they are on the same line)
    at index 5*i+2 - length: the length of the token.
    at index 5*i+3 - tokenType: will be looked up in SemanticTokensLegend.tokenTypes. We currently ask that tokenType < 65536.
    at index 5*i+4 - tokenModifiers: each set bit will be looked up in SemanticTokensLegend.tokenModifiers
 */
data class SemanticTokensBuilder(val data: ArrayList<Int> = ArrayList(4096)) {
    private var lastLineStart = 0
    private var lastColumnStart = 0
    fun add(tok: Token, tokenType: Int, modifiers: Int) {
        add(tok.beginLine, tok.beginColumn, tok.image.length, tokenType, modifiers)
    }

    fun add(beginLine: Int, beginColumn: Int, length: Int, tokenType: Int, modifiers: Int) {
        data.ensureCapacity(data.size + 5)
        if (beginLine != lastLineStart)
            lastColumnStart = 0

        data.add(beginLine - lastLineStart)
        data.add(beginColumn - lastColumnStart)
        data.add(length)
        data.add(tokenType)
        data.add(modifiers)

        lastLineStart = beginLine
        lastColumnStart = beginColumn
    }
}
