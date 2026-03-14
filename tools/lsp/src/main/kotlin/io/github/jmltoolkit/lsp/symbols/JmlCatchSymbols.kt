package io.github.jmltoolkit.lsp.symbols

import com.github.javaparser.ast.CompilationUnit
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.body.*
import com.github.javaparser.ast.expr.VariableDeclarationExpr
import com.github.javaparser.ast.jml.body.*
import com.github.javaparser.ast.jml.clauses.*
import com.github.javaparser.ast.modules.ModuleDeclaration
import com.github.javaparser.ast.visitor.GenericVisitorAdapter
import io.github.jmltoolkit.lsp.asRange
import org.eclipse.lsp4j.DocumentSymbol
import org.eclipse.lsp4j.SymbolKind
import java.util.*

/**
 * Runs through an AST and gathers symbols within JML annotations.
 *
 * @author Alexander Weigl
 */
class JmlCatchSymbols : GenericVisitorAdapter<MutableList<DocumentSymbol>?, Unit?>() {
    override fun visit(n: CompilationUnit, arg: Unit?): MutableList<DocumentSymbol> {
        val children = acceptAll(n.types)
        return arrayListOf(
            DocumentSymbol(
                n.storage.get().fileName,
                SymbolKind.File,
                n.asRange, n.primaryType.map { it.name.asRange }.orElse(n.asRange), "", children
            )
        )
    }

    override fun visit(n: AnnotationDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        val children = acceptAll(n.members)
        return arrayListOf(
            DocumentSymbol(
                n.nameAsString,
                SymbolKind.Interface,
                n.asRange, n.name.asRange, "", children
            )
        )
    }

    override fun visit(n: AnnotationMemberDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        return arrayListOf(
            DocumentSymbol(
                n.nameAsString,
                SymbolKind.Field,
                n.asRange, n.name.asRange, ""
            )
        )
    }

    override fun visit(n: ClassOrInterfaceDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        val children = acceptAll(n.members)
        return arrayListOf(
            DocumentSymbol(
                n.nameAsString,
                if (n.isInterface) SymbolKind.Interface else SymbolKind.Class,
                n.asRange, n.name.asRange, "", children
            )
        )
    }

    private fun acceptAll(members: NodeList<*>?): MutableList<DocumentSymbol> {
        if (members == null) return arrayListOf()
        return members.flatMap { it.accept(this, null) ?: arrayListOf() }.toMutableList()
    }

    private fun <T : Node> acceptAllo(members: Optional<NodeList<T>>?): MutableList<DocumentSymbol> =
        acceptAll(members?.orElse(null))

    override fun visit(n: ConstructorDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        val children = acceptAll(n.contracts)
        return arrayListOf(
            DocumentSymbol(
                n.nameAsString,
                SymbolKind.Constructor,
                n.asRange, n.name.asRange, "", children
            )
        )
    }


    override fun visit(n: EnumConstantDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        return arrayListOf(
            DocumentSymbol(
                n.nameAsString,
                SymbolKind.EnumMember,
                n.asRange, n.name.asRange,
            )
        )
    }

    override fun visit(n: EnumDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        val children = acceptAll(n.members)
        return arrayListOf(
            DocumentSymbol(
                n.nameAsString,
                SymbolKind.Enum,
                n.asRange, n.name.asRange, "", children
            )
        )
    }

    override fun visit(n: FieldDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        return n.variables.map {
            DocumentSymbol(
                it.nameAsString,
                SymbolKind.Field,
                it.asRange, it.name.asRange, it.typeAsString, arrayListOf()
            )
        }.toMutableList()
    }

    override fun visit(n: MethodDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        val children = acceptAll(n.contracts)
        return arrayListOf(
            DocumentSymbol(
                n.nameAsString,
                SymbolKind.Method,
                n.asRange, n.name.asRange, "", children
            )
        )
    }

    override fun visit(n: JmlMethodDeclaration, arg: Unit?): MutableList<DocumentSymbol>? {
        return n.methodDeclaration.accept(this, arg)
    }

    override fun visit(n: VariableDeclarationExpr?, arg: Unit?): MutableList<DocumentSymbol>? {
        return super.visit(n, arg)
    }

    override fun visit(n: ModuleDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        return arrayListOf(
            DocumentSymbol(
                n.nameAsString,
                SymbolKind.Module,
                n.asRange, n.name.asRange, "", arrayListOf()
            )
        )
    }

    override fun visit(n: JmlContract, arg: Unit?): MutableList<DocumentSymbol> {
        val children = acceptAll(n.subContracts) + acceptAll(n.clauses)
        return arrayListOf(
            DocumentSymbol(
                n.name.map { it.asString() }.orElse(n.behavior.asString()),
                SymbolKind.Key,
                n.asRange, n.asRange, "${n.jmlTags}", children
            )
        )
    }

    override fun visit(n: JmlRepresentsDeclaration?, arg: Unit?): MutableList<DocumentSymbol> {
        return arrayListOf()//return super.visit(n, arg)
    }

    override fun visit(n: JmlFieldDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        val decl = n.decl
        return decl.variables.map { v ->
            DocumentSymbol(
                v.nameAsString,
                SymbolKind.Property,
                n.asRange, n.asRange, "Jml model method: activated with ${n.jmlTags}", listOf()
            )
        }.toMutableList()

    }

    override fun visit(n: JmlClassAccessibleDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        return arrayListOf() //super.visit(n, arg)
    }

    override fun visit(n: JmlClassExprDeclaration, arg: Unit?): MutableList<DocumentSymbol> {
        return arrayListOf(
            DocumentSymbol(
                n.name.map { it.asString() }.orElse("anon invariant"),
                SymbolKind.Property,
                n.asRange, n.asRange, "Jml class invariant", listOf()
            )
        )
    }

    override fun visit(n: JmlSimpleExprClause, arg: Unit?): MutableList<DocumentSymbol> {
        return arrayListOf(
            DocumentSymbol(
                n.name.map { "$it : ${n.kind}" }.orElse("Clause ${n.kind}"),
                SymbolKind.EnumMember,
                n.asRange, n.asRange, "Jml clause", listOf()
            )
        )
    }

    override fun visit(n: JmlSignalsClause?, arg: Unit?): MutableList<DocumentSymbol>? {
        return super.visit(n, arg)
    }

    override fun visit(n: JmlSignalsOnlyClause?, arg: Unit?): MutableList<DocumentSymbol>? {
        return super.visit(n, arg)
    }

    override fun visit(n: JmlCallableClause?, arg: Unit?): MutableList<DocumentSymbol>? {
        return super.visit(n, arg)
    }

    override fun visit(n: JmlForallClause?, arg: Unit?): MutableList<DocumentSymbol>? {
        return super.visit(n, arg)
    }

    override fun visit(n: JmlClauseIf?, arg: Unit?): MutableList<DocumentSymbol>? {
        return super.visit(n, arg)
    }

    override fun visit(n: JmlOldClause?, arg: Unit?): MutableList<DocumentSymbol>? {
        return super.visit(n, arg)
    }

    override fun visit(n: JmlMultiExprClause?, arg: Unit?): MutableList<DocumentSymbol>? {
        return super.visit(n, arg)
    }
}
