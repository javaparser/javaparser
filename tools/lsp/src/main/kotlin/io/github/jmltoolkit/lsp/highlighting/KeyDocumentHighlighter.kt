package io.github.jmltoolkit.lsp.highlighting

import de.uka.ilkd.key.nparser.KeYLexer
import de.uka.ilkd.key.nparser.ParsingFacade
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Token
import org.eclipse.lsp4j.SemanticTokens

class KeyDocumentHighlighter : DocumentHighlighter {
    override fun analyzeJmlToken(text: String): SemanticTokens {
        val lexer = ParsingFacade.createLexer(CharStreams.fromString(text))
        val tb = SemanticTokensBuilder()
        do {
            val token = lexer.nextToken()
            if (token.type == KeYLexer.EOF) {
                break
            }
            tokenType(token)?.let { tt ->
                tb.add(token.line, token.charPositionInLine, token.text.length, tt, tokenModifier(token))
            }
        } while (token.type == KeYLexer.EOF)
        return SemanticTokens(tb.data)
    }

    private fun tokenType(token: Token): Int? {
        return when (token.type) {
            KeYLexer.COMMENT -> SupportedTokenTypes.COMMENT.ordinal
            KeYLexer.VARIABLE -> SupportedTokenTypes.VARIABLE.ordinal
            KeYLexer.VARCOND,
            KeYLexer.IF,
            KeYLexer.IFEX,
            KeYLexer.RULES,
            KeYLexer.AXIOMS,
            KeYLexer.ABSTRACT,
            KeYLexer.ASSIGN,
            KeYLexer.ASSUMES,
            KeYLexer.ADD,
            KeYLexer.FIND,
            KeYLexer.FINAL,
            KeYLexer.ANTECEDENTPOLARITY,
            KeYLexer.SUCCEDENTPOLARITY,
            KeYLexer.UPDATE,
            KeYLexer.UNIQUE,
            KeYLexer.FUNCTIONS,
            KeYLexer.PREDICATES,
            KeYLexer.SORTS,
            KeYLexer.HASSORT,
            KeYLexer.HAS_INVARIANT,
            KeYLexer.AT,
            KeYLexer.THEN,
            KeYLexer.TERM,
            KeYLexer.DIFFERENT,
            KeYLexer.CONTRACTS,
            KeYLexer.CONTAINERTYPE,
            KeYLexer.ENUM_CONST,
            KeYLexer.IS_LABELED,
            KeYLexer.IS_ABSTRACT_OR_INTERFACE,
            KeYLexer.ISCONSTANT,
            KeYLexer.ONEOF,
            KeYLexer.OPTIONSDECL,
            KeYLexer.WITHOPTIONS,
            KeYLexer.MODALITYB,
            KeYLexer.MORE,
            KeYLexer.MODALITY,
            KeYLexer.MODIFIABLE,
            KeYLexer.APPLY_UPDATE_ON_RIGID,
            KeYLexer.ADDRULES,
            -> SupportedTokenTypes.KEYWORD.ordinal

            KeYLexer.BIN_LITERAL,
            KeYLexer.HEX_LITERAL,
            KeYLexer.INT_LITERAL,
            KeYLexer.CHAR_LITERAL,
            KeYLexer.REAL_LITERAL,
            KeYLexer.DOUBLE_LITERAL,
            KeYLexer.FLOAT_LITERAL,
            KeYLexer.STRING_LITERAL,
            KeYLexer.QUOTED_STRING_LITERAL,
            -> SupportedTokenTypes.NUMBER.ordinal
            else -> null
        }
    }

    private fun tokenModifier(token: Token): Int = when (token.type) {
        else -> 0
    }

}