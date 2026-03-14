package io.github.jmltoolkit.lsp

import com.github.javaparser.ast.jml.clauses.ContractType
import com.github.javaparser.ast.jml.clauses.JmlContract
import io.github.jmltoolkit.lsp.actions.VerifyAgainstParent
import org.eclipse.lsp4j.CodeLens
import org.eclipse.lsp4j.Command

/**
 * Runs through the AST and collect code lens actions.
 */
class CodeLensCollector : ResultingVisitor<MutableList<out CodeLens>>() {
    override val result = arrayListOf<CodeLens>()

    override fun visit(n: JmlContract, arg: Unit?) {
        if (n.type == ContractType.METHOD) {
            //result.add(VerifyAgainstParent.createCodeLens(n))
        }
    }
}
