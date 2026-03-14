package io.github.jmltoolkit.lsp.highlighting

import com.github.javaparser.*
import com.github.javaparser.GeneratedJavaParserConstants.EOF
import com.github.javaparser.jml.JmlDocSanitizer
import org.eclipse.lsp4j.SemanticTokens

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.01.24)
 */
class JmlDocumentHighlighter : DocumentHighlighter {
    private fun analyzeJmlToken(result: SemanticTokensBuilder, tokens: MutableList<Token>) {
        val sanitizer = JmlDocSanitizer(setOf())
        val text = sanitizer.asString(tokens, true)
        val lexer = GeneratedJavaParserTokenManager(
            SimpleCharStream(Providers.provider(text)),
            GeneratedJavaParserConstants.JML_MULTI_CONTRACT
        )

        do {
            val token = lexer.nextToken
            val tokenType = tokenType(token)
            if (tokenType != null)
                result.add(token, tokenType, tokenModifier(token))
        } while (token.kind != EOF)
    }

    private fun tokenType(token: Token): Int? {
        val cat = TokenTypes.getCategory(token.kind)
        return when (cat) {
            JavaToken.Category.COMMENT -> SupportedTokenTypes.COMMENT.ordinal
            JavaToken.Category.IDENTIFIER -> SupportedTokenTypes.VARIABLE.ordinal
            JavaToken.Category.KEYWORD -> SupportedTokenTypes.KEYWORD.ordinal
            JavaToken.Category.LITERAL -> SupportedTokenTypes.NUMBER.ordinal
            else -> null
        }
    }

    private fun tokenModifier(token: Token): Int = when (token.kind) {
        else -> 0
    }

    override fun analyzeJmlToken(text: String): SemanticTokens {
        val provider = Providers.provider(text)
        val lexer = GeneratedJavaParserTokenManager(SimpleCharStream(provider))
        val result = SemanticTokensBuilder()
        var token = lexer.nextToken
        val bag = mutableListOf<Token>()
        while (token != null && token.kind != EOF) {
            when (token.kind) {
                GeneratedJavaParserConstants.JML_LINE_COMMENT,
                GeneratedJavaParserConstants.JML_BLOCK_COMMENT -> {
                    bag.add(token)
                }
            }
            token = lexer.nextToken
        }
        analyzeJmlToken(result, bag)
        return SemanticTokens(result.data)
    }
}