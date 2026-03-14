package io.github.jmltoolkit.lint


/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
data class JmlLintingConfig(val checkNameClashes: Boolean = true, val checkMissingNames: Boolean = true) {
    fun isDisabled(lintRule: LintRule): Boolean {
        return false
    }
}
