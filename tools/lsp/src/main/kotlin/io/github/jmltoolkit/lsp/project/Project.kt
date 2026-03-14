package io.github.jmltoolkit.lsp.project

import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.exists
import kotlin.io.path.readText
import kotlin.io.path.writeText

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.02.24)
 */
object Project {
    private const val FILENAME = "jmlproject.json"

    @OptIn(ExperimentalSerializationApi::class)
    private val json = Json {
        prettyPrint = true
        this.isLenient = true
        this.encodeDefaults = true
        this.allowStructuredMapKeys = true
        this.allowTrailingComma = true
        this.coerceInputValues = true
        this.ignoreUnknownKeys = true
    }

    fun save(path: Path, pd: ProjectDefinition): Path {
        val string = json.encodeToString(pd)
        path.writeText(string)
        return path
    }

    fun read(path: Path): ProjectDefinition =
        json.decodeFromString<ProjectDefinition>(path.readText())

    fun create(path: Path): Path =
        path.resolve(FILENAME).let {
            if (!it.exists()) save(it, ProjectDefinition())
            it
        }


    tailrec fun find(path: Path): Path? {
        val candidate = path.resolve(FILENAME)
        return if (Files.exists(candidate)) {
            candidate
        } else {
            find(path.parent)
        }
    }
}