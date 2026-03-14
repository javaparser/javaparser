package io.github.jmltoolkit.lsp.project

import io.github.jmltoolkit.lsp.actions.VerifyAgainstParent
import io.github.jmltoolkit.lsp.actions.WellDefinednessCheck
import kotlinx.serialization.Serializable

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.02.24)
 */
@Serializable
data class ProjectDefinition(
    var enabledKeys: Set<String> = setOf(),
    var usedKeys: Set<Set<String>> = setOf(),
    var sourcePaths: List<SourcePath> = listOf(),
    var disabledLinter: Set<String> = setOf(),
    var disabledCodeActions: Set<String> = setOf(
        VerifyAgainstParent.id,
        WellDefinednessCheck.id,
    ),
)

@Serializable
data class SourcePath(var path: String, var dependsOn: List<String> = listOf())
