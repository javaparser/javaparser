package io.github.jmltoolkit.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context

/**
 * @author Alexander Weigl
 * @version 1 (09.04.23)
 */

class XPathCommand : CliktCommand(name = "xpath") {
    override fun help(context: Context): String {
        return "Evaluate XPath queries on a set of Java/JML files."
    }

    override fun run() {
        TODO("Not yet implemented")
    }
}
