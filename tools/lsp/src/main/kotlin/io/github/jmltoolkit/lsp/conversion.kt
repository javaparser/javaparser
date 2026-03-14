package io.github.jmltoolkit.lsp

import com.github.javaparser.JavaToken
import com.github.javaparser.TokenRange
import com.github.javaparser.ast.Node
import org.eclipse.lsp4j.Position
import org.eclipse.lsp4j.Range
import java.util.*
import kotlin.jvm.optionals.getOrNull


val com.github.javaparser.Position.asPosition: Position
    get() = Position(line - 1, column - 1)

val Optional<TokenRange>.asRange: Range
    get() =
        if (isPresent) {
            val r = get().toRange().get()
            r.asRange
        } else {
            Range(Position(-1, -1), Position(-1, 0))
        }

fun Optional<com.github.javaparser.Range>.asRange(): Range =
    if (isPresent) {
        this.get().asRange
    } else {
        Range()
    }

val com.github.javaparser.Range.asRange: Range
    get() = Range(begin.asPosition, end.withColumn(end.column + 1).asPosition)

val Node.asRange: Range
    get() = range.asRange()

val Range.asRange: com.github.javaparser.Range
    get() = com.github.javaparser.Range(start.asPosition, end.asPosition)

val Position?.toPosition: com.github.javaparser.Position?
    get() = this?.asPosition
val Position.asPosition: com.github.javaparser.Position
    get() = com.github.javaparser.Position(this.line + 1, this.character + 1)


private val JavaToken.asStartPosition: Position?
    get() = this.range.getOrNull()?.asStartPosition


val com.github.javaparser.Range.asStartPosition: Position
    get() = this.begin.asPosition

val com.github.javaparser.Range.asEndPosition: Position
    get() = this.end.asPosition

val JavaToken.asEndPosition: Position?
    get() = this.range.getOrNull()?.asEndPosition

val TokenRange?.asRange: Range?
    get() = this?.let { Range(begin.asStartPosition, end.asEndPosition) }
