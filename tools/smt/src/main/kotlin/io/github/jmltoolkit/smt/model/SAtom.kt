package io.github.jmltoolkit.smt.model

import com.github.javaparser.resolution.types.ResolvedType
import java.io.PrintWriter

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
class SAtom(stype: SmtType?, javaType: ResolvedType?, val value: String) : SExpr(javaType, stype) {
    override fun appendTo(writer: PrintWriter) {
        writer.write(value)
    }
}
