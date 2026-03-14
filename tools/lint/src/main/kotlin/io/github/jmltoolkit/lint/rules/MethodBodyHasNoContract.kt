package io.github.jmltoolkit.lint.rules

import com.github.javaparser.ast.body.MethodDeclaration
import com.github.javaparser.ast.validator.ProblemReporter
import com.github.javaparser.ast.validator.VisitorValidator

class MethodBodyHasNoContract : VisitorValidator() {
    override fun visit(n: MethodDeclaration, arg: ProblemReporter) {
        if (n.body.isPresent && !n.body.get().contracts.isEmpty()) {
            arg.report(n, "Body of method has a block contract.")
        }
        super.visit(n, arg)
    }
}
