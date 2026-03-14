package io.github.jmltoolkit.stat

import com.github.javaparser.ast.CompilationUnit
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.body.*
import com.github.javaparser.ast.expr.*
import com.github.javaparser.ast.jml.NodeWithJmlTags
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration
import com.github.javaparser.ast.jml.body.JmlFieldDeclaration
import com.github.javaparser.ast.jml.body.JmlMethodDeclaration
import com.github.javaparser.ast.jml.body.JmlRepresentsDeclaration
import com.github.javaparser.ast.jml.clauses.*
import com.github.javaparser.ast.jml.doc.*
import com.github.javaparser.ast.jml.expr.*
import com.github.javaparser.ast.jml.stmt.*
import com.github.javaparser.ast.modules.ModuleDeclaration
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers
import com.github.javaparser.ast.nodeTypes.NodeWithName
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt
import com.github.javaparser.ast.visitor.GenericVisitorAdapter
import com.github.javaparser.ast.visitor.VoidVisitorAdapter
import com.github.javaparser.jml.JmlDocSanitizer
import org.w3c.dom.Document
import org.w3c.dom.Element
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (24.05.22)
 */
class StatVisitor(
    private val xmlDocument: Document,
    private val keys: List<String>,
    private val expressionCosts: ExpressionCosts
) : VoidVisitorAdapter<Element>() {
    //region Java Stuff
    override fun visit(n: CompilationUnit, arg: Element) {
        super.visit(n, newJavaContext(arg, n.javaClass.getSimpleName(), n.storage.get().fileName))
    }

    override fun visit(n: MethodDeclaration, arg: Element) {
        val arg = newJavaContext(
            arg, n.javaClass.getSimpleName(),
            n.getDeclarationAsString(false, false, true)
        )
        super.visit(n, arg)
    }

    override fun visit(n: ClassOrInterfaceDeclaration, arg: Element) {
        val e = newJavaContext(arg, n)
        super.visit(n, e)
    }

    override fun visit(n: ConstructorDeclaration, arg: Element) {
        var e = newJavaContext(
            arg, n.javaClass.getSimpleName(),
            n.getDeclarationAsString(false, false, true)
        )
        super.visit(n, e)
    }

    override fun visit(n: AnnotationDeclaration, arg: Element) {
        val e = newJavaContext(arg, n)
        super.visit(n, e)
    }

    override fun visit(n: AnnotationMemberDeclaration, arg: Element) {
        super.visit(n, arg)
    }

    override fun visit(n: EnumDeclaration, arg: Element) {
        super.visit(n, newJavaContext(arg, n))
    }

    override fun visit(n: LocalClassDeclarationStmt, arg: Element) {
        super.visit(n, arg)
    }

    override fun visit(n: ModuleDeclaration, arg: Element) {
        super.visit(n, newJavaContext(arg, n))
    }

    private fun newJavaContext(parent: Element, node: NodeWithName<*>): Element =
        newJavaContext(parent, node.javaClass.getSimpleName(), node.nameAsString)

    private fun newJavaContext(parent: Element, node: NodeWithSimpleName<*>): Element =
        newJavaContext(parent, node.javaClass.getSimpleName(), node.nameAsString)

    private fun newJavaContext(parent: Element, simpleName: String, name: String): Element {
        val e = xmlDocument.createElement(simpleName)
        e.setAttribute("name", name)
        parent.appendChild(e)
        return e
    }

    //endregion
    //region plain text reporting
    override fun visit(n: JmlDocDeclaration, arg: Element) {
        reportPlainText(n, arg)
    }

    override fun visit(n: JmlDoc, arg: Element) {
    }

    override fun visit(n: JmlDocStmt, arg: Element) {
        reportPlainText(n, arg)
    }

    override fun visit(n: JmlDocType, arg: Element) {
        reportPlainText(n, arg)
    }

    private fun reportPlainText(n: JmlDocContainer, arg: Element) {
        val doc = JmlDocSanitizer(keys.toSet())
        val san: String = doc.asString(n.jmlComments, false)
        val newlines = newlines(san)
        val e = xmlDocument.createElement("jml-comment")
        arg.appendChild(e)
        e.setAttribute("newlines", "" + newlines)
        e.setAttribute("type", n.javaClass.getSimpleName())
        e.setAttribute("chars", "" + san.length)
    }

    //endregion
    override fun visit(n: JmlClassExprDeclaration, arg: Element) {
        if (active(n)) {
            val e = newElement(arg, n.kind.identifier)
            val expr = getExpressionStat(n.invariant)
            e.appendChild(expr)
            if (n.name.isPresent) {
                e.setAttribute("name", n.name.get().asString())
            }
            setModifierAsAttributes(n, e)
        }
    }

    private fun setModifierAsAttributes(n: NodeWithModifiers<*>, e: Element) {
        for (modifier in n.modifiers) {
            e.setAttribute("has" + modifier.keyword.asString(), "true")
        }
    }

    private fun getExpressionStat(expr: Expression): Element {
        val e = xmlDocument.createElement("expr")
        val costs: Int = expr.accept(ExpressionComplexity(), expressionCosts)
        val numOfVariables = numberOfVariables(expr)
        val length = lengthOf(expr)
        e.setAttribute("complexity", "" + costs)
        e.setAttribute("numOfVariables", "" + numOfVariables)
        e.setAttribute("length", "" + length)

        val map = count(expr)
        map.forEach { k, v -> e.setAttribute(k.simpleName, "" + v) }
        return e
    }

    private fun lengthOf(expr: Expression): Int = expr.toString().length

    private fun numberOfVariables(expr: Expression): Int {
        var sum = 0
        for (childNode in expr.childNodes) {
            if (childNode is NameExpr) sum++
            else if (childNode is Expression && !childNode.getChildNodes().isEmpty()) {
                sum += numberOfVariables(childNode)
            }
        }
        return sum
    }

    private fun newElement(parent: Element, tag: String): Element {
        val e = xmlDocument.createElement(tag)
        parent.appendChild(e)
        return e
    }

    private fun active(n: NodeWithJmlTags<*>): Boolean = equal(keys, n.jmlTags)


    override fun visit(n: JmlRepresentsDeclaration, arg: Element) {
        if (active(n)) {
            val a = newElement(arg, "represents")
            a.setAttribute("name", n.nameAsString)
            setModifierAsAttributes(n, a)
        }
    }

    override fun visit(n: JmlMethodDeclaration, arg: Element) {
        var e = arg
        if (active(n)) {
            e = newJavaContext(e, n.javaClass.getSimpleName(), n.methodDeclaration.nameAsString)
            setModifierAsAttributes(n.methodDeclaration, e)
            super.visit(n.methodDeclaration, e)
        }
    }


    override fun visit(n: JmlContract, arg: Element) {
        if (active(n)) {
            var name = "contract_" + n.range.get().begin.line
            if (n.name.isPresent) {
                name = n.name.get().identifier
            }
            val e = newJavaContext(arg, n.javaClass.getSimpleName(), name)
            e.setAttribute("type", n.type.toString())
            setModifierAsAttributes(n, e)
            e.setAttribute("behavior", "" + n.behavior)
            super.visit(n, e)
        }
    }

    override fun visit(n: JmlExpressionStmt, arg: Element) {
        if (active(n)) {
            val e = newElement(arg, n.kind.jmlSymbol())
            e.appendChild(getExpressionStat(n.expression))
        }
    }

    override fun visit(n: JmlUnreachableStmt, arg: Element) {
        if (active(n)) {
            val e = newElement(arg, "jml-unreachable")
        }
    }

    override fun visit(n: JmlBeginStmt, arg: Element) {
        if (active(n)) {
            newElement(arg, "jml-begin")
        }
    }

    override fun visit(n: JmlEndStmt, arg: Element) {
        if (active(n)) {
            newElement(arg, "jml-end")
        }
    }

    override fun visit(n: JmlGhostStmt, arg: Element) {
        if (active(n)) {
            val e = newElement(arg, "jml-ghost")
            e.setAttribute("statements", "")
            super.visit(n, e)
        }
    }


    override fun visit(n: JmlLabelStmt, arg: Element) {
        if (active(n)) {
            newElement(arg, "jml-label")
        }
    }

    override fun visit(n: JmlSimpleExprClause, arg: Element) {
        val e = newElement(arg, n.kind.jmlSymbol)
        e.appendChild(getExpressionStat(n.expression))
    }

    override fun visit(n: JmlSignalsClause, arg: Element) {
        newElement(arg, n.kind.jmlSymbol)
    }

    override fun visit(n: JmlSignalsOnlyClause, arg: Element) {
        val e = newElement(arg, n.kind.jmlSymbol)
        e.setAttribute("numOfTypes", "" + n.types.size)
    }

    override fun visit(n: JmlOldClause, arg: Element) {
        val e = newElement(arg, n.kind.jmlSymbol)
        e.setAttribute("numOfDecls", "" + n.declarations.variables.size)
    }

    override fun visit(n: JmlMultiExprClause, arg: Element) {
        val e = newElement(arg, n.kind.jmlSymbol)
        for (expression in n.expressions) {
            e.appendChild(getExpressionStat(expression))
        }
    }

    override fun visit(n: JmlCallableClause, arg: Element) {
        val e = newElement(arg, n.kind.jmlSymbol)
    }

    override fun visit(n: JmlForallClause, arg: Element) {
        val e = newElement(arg, n.kind.jmlSymbol)
        e.setAttribute("numVars", "" + n.boundedVariables.size)
    }

    override fun visit(n: JmlRefiningStmt, arg: Element) {
        if (active(n)) {
            val e = newElement(arg, "jml-refining")
        }
    }

    override fun visit(n: JmlClauseIf, arg: Element) {
        super.visit(n, arg)
    }

    override fun visit(n: JmlFieldDeclaration, arg: Element) {
        //update(n, this::update)
    }

    interface Update<R> {
        fun fn(parent: Element, node: R)
    }

    private fun <R : NodeWithJmlTags<*>> update(n: R, update: Update<R>) {
    }

    private fun update(parent: JmlFieldDeclaration, n: JmlFieldDeclaration) {
        /*if (n.getDecl().hasModifier(Modifier.DefaultKeyword.JML_GHOST)) {
            getClassStat(stat, n).addNumOfGhostFields(1);
        } else if (n.getDecl().hasModifier(Modifier.DefaultKeyword.JML_MODEL)) {
            getClassStat(stat, n).addNumOfModelFields(1);
        }
         */
    }


    private fun count(e: Expression): Map<Class<*>, Int> {
        val occCounter: MutableMap<Class<*>, Int> = HashMap()
        val q: ArrayDeque<Node> = ArrayDeque<Node>()
        q.add(e)

        while (!q.isEmpty()) {
            val n: Node = q.pop()
            occCounter.compute(n.javaClass) { k: Class<*>, i: Int? -> i?.let { it + 1 } ?: 1 }
            for (childNode in n.childNodes) {
                if (childNode is Expression) {
                    q.add(childNode)
                }
            }
        }
        return occCounter
    }

    companion object {
        private fun newlines(text: String): Int {
            val chars = text.toCharArray()
            var n = 0
            for (aChar in chars) {
                if (aChar == '\n') {
                    n++
                }
            }
            return n
        }


        private fun equal(keySet: List<String>, jmlTags: NodeList<SimpleName>): Boolean {
            if (keySet.size != jmlTags.size) {
                return false
            }

            for (i in keySet.indices) {
                if (keySet[i] != jmlTags.get(i).identifier) {
                    return false
                }
            }
            return true
        }
    }
}

internal class ExpressionComplexity : GenericVisitorAdapter<Int, ExpressionCosts>() {
    override fun visit(n: ArrayAccessExpr, arg: ExpressionCosts): Int = super.visit(n, arg)

    override fun visit(n: ArrayCreationExpr, arg: ExpressionCosts): Int = super.visit(n, arg)

    override fun visit(n: ArrayInitializerExpr, arg: ExpressionCosts): Int = super.visit(n, arg)

    override fun visit(n: AssignExpr, arg: ExpressionCosts): Int =
        arg.assign + n.target.accept(this, arg) + n.value.accept(this, arg)

    override fun visit(n: BinaryExpr, arg: ExpressionCosts): Int =
        //TODO distinguish by operator
        arg.minus + n.left.accept(this, arg) + n.right.accept(this, arg)

    override fun visit(n: UnaryExpr, arg: ExpressionCosts): Int = super.visit(n, arg)

    override fun visit(n: LambdaExpr, arg: ExpressionCosts): Int = super.visit(n, arg)

    override fun visit(n: CastExpr, arg: ExpressionCosts): Int = arg.cast + n.expression.accept(this, arg)

    override fun visit(n: CharLiteralExpr, arg: ExpressionCosts): Int = arg.charLiteral

    override fun visit(n: ConditionalExpr, arg: ExpressionCosts): Int {
        return arg.conditional + n.condition.accept(this, arg) + n.thenExpr
            .accept(this, arg) + n.elseExpr.accept(
            this, arg
        )
    }

    override fun visit(n: EnclosedExpr, arg: ExpressionCosts): Int = n.inner.accept(this, arg)

    override fun visit(n: IntegerLiteralExpr, arg: ExpressionCosts): Int = arg.integerLiteral

    override fun visit(n: LongLiteralExpr, arg: ExpressionCosts): Int = arg.longLiteral

    override fun visit(n: MethodCallExpr, arg: ExpressionCosts): Int = arg.methodCall + sum(n.arguments, arg)

    override fun visit(n: NameExpr, arg: ExpressionCosts): Int = arg.name

    override fun visit(n: NullLiteralExpr, arg: ExpressionCosts): Int = arg.nullLiteral

    override fun visit(n: JmlQuantifiedExpr, arg: ExpressionCosts): Int =
        arg.quantor + n.variables.size * arg.binderCostsPerVariable + sum(n.expressions, arg)

    private fun sum(n: NodeList<Expression>, arg: ExpressionCosts): Int {
        return n.stream().mapToInt { it -> Objects.requireNonNull(it.accept(this, arg), it.javaClass.getSimpleName()) }
            .sum()
    }

    override fun visit(n: JmlTypeExpr, arg: ExpressionCosts): Int = 1

    override fun visit(n: SuperExpr, arg: ExpressionCosts): Int = 0

    override fun visit(n: SwitchExpr, arg: ExpressionCosts): Int {
        return n.selector.accept(this, arg) + n.entries.stream()
            .mapToInt { it -> sum(it.labels, arg) + 1 }
            .sum()
    }

    override fun visit(n: TypePatternExpr, arg: ExpressionCosts): Int = 0
    override fun visit(n: RecordPatternExpr, arg: ExpressionCosts?): Int = super.visit(n, arg)

    override fun visit(n: BooleanLiteralExpr, arg: ExpressionCosts): Int = 0

    override fun visit(n: InstanceOfExpr, arg: ExpressionCosts): Int = arg.instanceof + n.expression.accept(this, arg)

    override fun visit(n: JmlLabelExpr, arg: ExpressionCosts): Int = super.visit(n, arg)

    override fun visit(n: JmlLetExpr, arg: ExpressionCosts): Int =
        arg.let + arg.binderCostsPerVariable * n.variables.variables.size

    override fun visit(n: JmlMultiCompareExpr, arg: ExpressionCosts): Int = arg.compare * n.operators.size
}