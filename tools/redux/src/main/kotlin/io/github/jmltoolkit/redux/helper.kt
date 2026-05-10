package io.github.jmltoolkit.redux

import com.github.javaparser.StaticJavaParser
import com.github.javaparser.ast.body.BodyDeclaration
import com.github.javaparser.ast.body.TypeDeclaration
import com.github.javaparser.ast.expr.StringLiteralExpr
import com.github.javaparser.ast.jml.NodeWithContracts
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations
import javax.annotation.processing.Generated

/**
 * 
 * @author Alexander Weigl 
 * @version 1 (02.05.26)
 */
fun addGenerated(node: NodeWithAnnotations<*>, text: String) {
    node.addSingleMemberAnnotation(
        Generated::class.java.getName(),
        StringLiteralExpr(text)
    )
}

fun attachTypeSpec(clazz: TypeDeclaration<*>, spec: String?) {
    if (spec == null) return
    val specification = StaticJavaParser.parseJmlClassLevel(spec)
    for (node in specification.children) {
        clazz.addMember(node as BodyDeclaration<*>)
    }
}

fun attachContract(node: NodeWithContracts<*>, spec: String?) {
    if (spec == null) return
    val specification = StaticJavaParser.parseJmlContract(spec)
    node.addContract(specification)
}
