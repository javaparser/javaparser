package io.github.jmltoolkit.lint

import com.github.javaparser.ast.Node
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import se.bjurr.violations.lib.model.generated.sarif.*
import java.util.*
import java.util.function.Consumer
import kotlin.Exception

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
class JmlLintingFacade(private val config: JmlLintingConfig) {
    val linters: List<LintRule> = getLinter(config)

    private val sarifTool: Tool
        get() = Tool().withDriver(
            ToolComponent().withVersion(VERSION).withName(NAME)
                .withShortDescription(MultiformatMessageString().withText("Linting for the Java Modeling Language"))
                .withRules(linters.map { ReportingDescriptor().withName(it.javaClass.getName()) }.toSet())
        )


    fun lint(reporter: LintProblemReporter, nodes: Collection<Node>) {
        for (it in nodes) {
            for (linter in linters) {
                try {
                    linter.accept(it, reporter, config)
                } catch (e: Exception) {
                    LOGGER.error("Error in linter: {}", linter.javaClass.getName(), e)
                }
            }
        }
    }

    fun lint(nodes: Collection<Node>): Collection<LintProblem> {
        val problems: ArrayList<LintProblem> = ArrayList<LintProblem>(1024)
        val collector: Consumer<LintProblem> = Consumer<LintProblem> { e: LintProblem -> problems.add(e) }
        lint(LintProblemReporter(collector), nodes)
        problems.sortWith(Comparator.comparing { it.location!!.toRange().get().begin })
        return problems
    }

    fun asSarif(problems: Collection<LintProblem>): SarifSchema {
        val results = problems.map { it: LintProblem -> this.asSarif(it) }
        val runs: List<Run> = listOf(Run().withTool(sarifTool).withResults(results))
        return SarifSchema()
            .withVersion("2.1.0")
            .withRuns(runs)
    }

    private fun asSarif(it: LintProblem): Result {
        return Result().withRuleId(it.ruleId).withKind(it.category).withLevel(it.level)
            .withLocations(listOf(Location())).withMessage(Message().withText(it.message))
    }

    companion object {
        private val LOGGER: Logger = LoggerFactory.getLogger(JmlLintingFacade::class.java)
        private val VERSION: String = JmlLintingFacade::class.java.getPackage().implementationVersion ?: "n/a"
        private const val NAME = "JML-lint"

        private fun getLinter(config: JmlLintingConfig): List<LintRule> {
            val loader: ServiceLoader<LintRule> = ServiceLoader.load(LintRule::class.java)
            val validators: MutableList<LintRule> = ArrayList<LintRule>(64)
            for (lintRule in loader) {
                if (!config.isDisabled(lintRule)) {
                    validators.add(lintRule)
                }
            }
            return validators
        }
    }
}
