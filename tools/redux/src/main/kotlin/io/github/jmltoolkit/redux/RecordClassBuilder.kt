/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package io.github.jmltoolkit.redux

import com.github.javaparser.StaticJavaParser.parseStatement
import com.github.javaparser.StaticJavaParser.parseType
import com.github.javaparser.ast.Modifier
import com.github.javaparser.ast.Modifier.DefaultKeyword
import com.github.javaparser.ast.Modifier.DefaultKeyword.PUBLIC
import com.github.javaparser.ast.Modifier.DefaultKeyword.STATIC
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration
import com.github.javaparser.ast.body.ConstructorDeclaration
import com.github.javaparser.ast.body.Parameter
import com.github.javaparser.ast.body.RecordDeclaration
import com.github.javaparser.ast.expr.*
import com.github.javaparser.ast.expr.BinaryExpr.Operator.AND
import com.github.javaparser.ast.expr.BinaryExpr.Operator.EQUALS
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration
import com.github.javaparser.ast.jml.doc.JmlDocModifier
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr
import com.github.javaparser.ast.stmt.ReturnStmt
import com.github.javaparser.ast.type.PrimitiveType
import java.util.*

/** This transformation is made to transform any found [RecordDeclaration] into a corresponding
 * [ClassOrInterfaceDeclaration].
 * 
 * @author weigl
 * @see [Java SE 25](https://docs.oracle.com/en/java/javase/25/language/records.html)
 * @since 2026-03-11
 */
class RecordClassBuilder(
    val addSpecification: Boolean = true,
    val addBodies: Boolean = true,
    val useInvariantFree: Boolean = true
) : Transformer {

    private val invariantKind = if (useInvariantFree) "invariant_free" else "axiom"

    override fun apply(a: Node): Node = if (a is RecordDeclaration) transform(a) else a

    private fun transform(recordDeclaration: RecordDeclaration): ClassOrInterfaceDeclaration {
        val clazz = ClassOrInterfaceDeclaration()
        clazz.setModifiers(recordDeclaration.modifiers)
        clazz.addModifier(DefaultKeyword.FINAL)
        if (clazz.isNestedType || clazz.isLocalClassDeclaration) {
            clazz.addModifier(STATIC) // do not have a pointer to the outer this.
        }
        clazz.setName(recordDeclaration.name)
        clazz.addExtendedType(Record::class.java)
        addGenerated(clazz, javaClass.simpleName)

        for (parameter in recordDeclaration.parameters) {
            val field =
                clazz.addField(
                    parameter.type(),
                    parameter.nameAsString,
                    DefaultKeyword.PRIVATE,
                    DefaultKeyword.FINAL
                )
            field.modifiers.addAll(parameter.modifiers)
            addGenerated(field, javaClass.simpleName)

            // only create a getter public final <type> <name>() { return <name>;}
            // unless there is no declaration in the record.
            if (recordDeclaration.getMethodsByName(parameter.nameAsString).isEmpty()) {
                val getter = clazz.addMethod(parameter.nameAsString)
                getter.setType(parameter.type())
                getter.addModifier(PUBLIC, DefaultKeyword.FINAL)
                for (mod in parameter.modifiers) {
                    if (mod.keyword is JmlDocModifier) {
                        getter.modifiers.add(mod.clone())
                    }
                }
                getter.body.get()
                    .addStatement(ReturnStmt(parameter.nameAsExpression))
                addGenerated(getter, javaClass.simpleName)
            }
        }

        createConstructor(recordDeclaration, clazz)

        val generated =
            createEquals(recordDeclaration, clazz) && createHashCode(recordDeclaration, clazz)

        if (generated && addSpecification) { // weigl: disabled, further discussion required.
            attachTypeSpecExpr(clazz) {
                equalFieldsEqualRecords(recordDeclaration, this)
            }

            val typeName = recordDeclaration.nameAsString
            attachTypeSpecExpr(clazz) {
                addModifier(PUBLIC, STATIC)
                kind = SimpleName("invariant_free")
                setName(SimpleName("eq_reflexivity"))

                val q = JmlQuantifiedExpr()
                q.binder = JmlQuantifiedExpr.JmlDefaultBinder.FORALL
                q.addParameter(typeName, "a")
                q.expressions.add(
                    MethodCallExpr(NameExpr("a"), SimpleName("equals"), NodeList(NameExpr("a")))
                )
                invariant = q

                this
            }

            attachTypeSpecExpr(clazz) {
                addModifier(PUBLIC, STATIC)
                kind = SimpleName("invariant_free")
                setName(SimpleName("eq_symm"))

                val q = JmlQuantifiedExpr()
                q.binder = JmlQuantifiedExpr.JmlDefaultBinder.FORALL
                q.addParameter(typeName, "a")
                q.addParameter(typeName, "b")
                q.expressions.add(
                    MethodCallExpr(NameExpr("a"), SimpleName("equals"), NodeList(NameExpr("b")))
                )
                q.expressions.add(
                    MethodCallExpr(NameExpr("b"), SimpleName("equals"), NodeList(NameExpr("a")))
                )
                invariant = q

                this
                //"public static invariant_free (\\forall %s a,b; a.equals(b); b.equals(a));"
            }

            attachTypeSpecExpr(clazz) {
                addModifier(PUBLIC, STATIC)
                kind = SimpleName("invariant_free")
                setName(SimpleName("eq_trans"))

                val q = JmlQuantifiedExpr()
                q.binder = JmlQuantifiedExpr.JmlDefaultBinder.FORALL
                q.addParameter(typeName, "a")
                q.addParameter(typeName, "b")
                q.addParameter(typeName, "c")
                val aequalsb = MethodCallExpr(NameExpr("a"), SimpleName("equals"), NodeList(NameExpr("b")))
                val bequalsc = MethodCallExpr(NameExpr("b"), SimpleName("equals"), NodeList(NameExpr("c")))
                val aequalsc = MethodCallExpr(NameExpr("b"), SimpleName("equals"), NodeList(NameExpr("c")))
                q.expressions.add(BinaryExpr(aequalsb, bequalsc, AND))
                q.expressions.add(aequalsc)
                invariant = q

                this
                //"public static invariant_free (\\forall $typeName a,b,c; a.equals(b) && b.equals(c); a.equals(c));"
            }

            attachTypeSpecExpr(clazz) {
                addModifier(PUBLIC, STATIC)
                kind = SimpleName("invariant_free")
                setName(SimpleName("eq_to_hash"))

                val q = JmlQuantifiedExpr()
                q.binder = JmlQuantifiedExpr.JmlDefaultBinder.FORALL
                q.addParameter(typeName, "a")
                q.addParameter(typeName, "b")
                val aequalsb = MethodCallExpr(NameExpr("a"), SimpleName("equals"), NodeList(NameExpr("b")))
                val ahash = MethodCallExpr(NameExpr("a"), SimpleName("hashCode"))
                val bhash = MethodCallExpr(NameExpr("b"), SimpleName("hashCode"))
                q.expressions.add(aequalsb)
                q.expressions.add(BinaryExpr(ahash, bhash, EQUALS))
                invariant = q

                this
                //"public static invariant_free (\\forall $typeName a,b; a.equals(b); a.hashCode() == b.hashCode());"
            }
        }

        createToString(recordDeclaration, clazz)

        clazz.members.addAll(recordDeclaration.members)
        return clazz
    }

    private fun attachTypeSpecExpr(
        clazz: ClassOrInterfaceDeclaration,
        fn: JmlClassExprDeclaration.() -> JmlClassExprDeclaration?
    ): JmlClassExprDeclaration? {
        val jml = JmlClassExprDeclaration().let { it.fn() }
        if (jml != null) {
            clazz.addMember(jml)
        }
        return jml
    }

    private fun createConstructor(
        recordDeclaration: RecordDeclaration,
        clazz: ClassOrInterfaceDeclaration
    ) {
        val paramTypes = recordDeclaration.parameters.map { it.type.asString() }.toTypedArray()
        val optConstructor = recordDeclaration.getConstructorByParameterTypes(*paramTypes)
        val fullConstructor: ConstructorDeclaration?
        if (optConstructor.isPresent) {
            fullConstructor = optConstructor.get()
        } else {
            fullConstructor = ConstructorDeclaration()
            fullConstructor.setName(recordDeclaration.nameAsString)
            fullConstructor.setModifiers(PUBLIC)
            addGenerated(fullConstructor, javaClass.simpleName)
            val body = fullConstructor.body.get()
            for (parameter in recordDeclaration.parameters) {
                val p = parameter.clone()
                fullConstructor.addParameter(p)
                body.addStatement("this.${p.nameAsString} = ${p.nameAsString};")
            }
        }

        for (compactConstructor in recordDeclaration.compactConstructors) {
            fullConstructor.body.get().statements.add(0, compactConstructor.body)
        }

        val fieldParamEqual = recordDeclaration.parameters
            .map { it.nameAsString }.map { "$it == this.$it" }
            .joinToString(" && ")

        attachContract(
            fullConstructor,
            """
                public normal_behavior
                requires true;
                ensures ${fieldParamEqual};
                assignable this.*;             
            """
        )
        clazz.addMember(fullConstructor)
    }

    private fun createToString(
        recordDeclaration: RecordDeclaration,
        clazz: ClassOrInterfaceDeclaration
    ) {
        val hasNoToString = recordDeclaration.getMethodsBySignature("toString").isEmpty()
        if (hasNoToString) {
            val toString =
                clazz.addMethod("toString", PUBLIC, DefaultKeyword.FINAL, DefaultKeyword.JML_NON_NULL)
            toString.addAnnotation(Override::class.java)
            toString.setType(String::class.java)
            val concatBuilder = ConcatBuilder()
            concatBuilder.addStr(clazz.nameAsString + "[")
            val parameters = recordDeclaration.parameters
            for (i in parameters.indices) {
                val parameter = parameters.get(i)
                concatBuilder.addStr(parameter.nameAsString + "=")
                concatBuilder.addVar(parameter.nameAsString)
                if (i < parameters.size - 1) {
                    concatBuilder.addStr(",")
                }
            }
            concatBuilder.addStr("]")
            toString.body.get().addStatement(ReturnStmt(concatBuilder.expr))
            addGenerated(toString, javaClass.simpleName)
        }
    }

    private fun createHashCode(
        recordDeclaration: RecordDeclaration,
        clazz: ClassOrInterfaceDeclaration
    ): Boolean {
        val hasNoHashcode = recordDeclaration.getMethodsBySignature("hashCode").isEmpty()
        if (hasNoHashcode) {
            val hashCode = clazz.addMethod("hashCode", PUBLIC, DefaultKeyword.FINAL)
            hashCode.addAnnotation(Override::class.java)
            hashCode.setType(Integer.TYPE)
            if (addBodies) {
                val args = recordDeclaration.parameters.map { it.nameAsExpression as Expression }
                hashCode.body.get()
                    .addStatement(ReturnStmt(callObjects("hash", NodeList(args))))
            } else {
                hashCode.setBody(null)
            }

            addGenerated(hashCode, javaClass.simpleName)

            attachContract(
                hashCode,
                """
                public normal_behavior
                ensures true; requires true;
                assignable \strictly_nothing;                  
                """
            )
        }
        return hasNoHashcode
    }

    private fun createEquals(
        recordDeclaration: RecordDeclaration,
        clazz: ClassOrInterfaceDeclaration
    ): Boolean {
        val hasNoEquals =
            recordDeclaration.getMethodsBySignature("equals", "java.lang.Object").isEmpty()
                    && recordDeclaration.getMethodsBySignature("equals", "Object").isEmpty()
        if (hasNoEquals) {
            val equals = clazz.addMethod("equals", PUBLIC, DefaultKeyword.FINAL)
            equals.addAnnotation(Override::class.java)
            equals.setType(java.lang.Boolean.TYPE)
            val tObject = parseType("java.lang.Object")
            val mods = NodeList<Modifier?>()
            equals.parameters.add(Parameter(mods, tObject, SimpleName("o")))
            equals.setBody(null)

            val typeName = recordDeclaration.nameAsString
            val idParams = recordDeclaration.parameters
                .map { it.nameAsString }
                .joinToString(" && ") { "this.$it==(($typeName)o).$it" }


            val eq2 = recordDeclaration.parameters
                .joinToString(" && ") {
                    val pname = it!!.nameAsString
                    if (it.type is PrimitiveType) "($pname == (($typeName)o).$pname)"
                    else "( this.$pname != null ? (this.$pname.equals((($typeName)o).$pname)) : (o.$pname == null))"
                }

            attachContract(
                equals, """
                    public normal_behavior
                    requires true;
                    ensures (
                                   (this == o) //equality of identity
                                || (o instanceof $typeName && o != null && $idParams)
                                || (o instanceof $typeName && o != null && $eq2)
                            ) <==> \result;
                    ensures hashCode() != o.hashCode() ==> !\result;
                    ensures o == null ==> !\result;
                    assignable \strictly_nothing;                  
                    """
            )


            val body = equals.body.get()
            body.addStatement(parseStatement("if(this == o) return true;"))
            body.addStatement(parseStatement("if(!(o instanceof ${clazz.nameAsString})) return false;"))
            body.addStatement(parseStatement("final ${clazz.nameAsString} that = (${clazz.nameAsString}) o;"))

            val equalFields = recordDeclaration.parameters
                .map { callObjects("equals", it.nameAsExpression, FieldAccessExpr(NameExpr("that"), it.nameAsString)) }
                .reduceOrNull { a, b -> BinaryExpr(a, b, AND) }

            body.addStatement(ReturnStmt(equalFields ?: BooleanLiteralExpr(true)))
            addGenerated(equals, javaClass.simpleName)
        }
        return hasNoEquals
    }

    private fun callObjects(method: String?, vararg exprs: Expression?): Expression {
        return callObjects(method, Arrays.stream<Expression?>(exprs).toList())
    }

    private fun callObjects(method: String?, exprs: MutableList<Expression?>?): Expression {
        val objects =
            FieldAccessExpr(FieldAccessExpr(NameExpr("java"), "lang"), "Objects")
        return MethodCallExpr(objects, method, NodeList(exprs))
    }

    private class ConcatBuilder {
        var expr: Expression? = null


        fun addStr(s: String?): ConcatBuilder {
            return concat(StringLiteralExpr(s))
        }

        fun concat(expr: Expression?): ConcatBuilder {
            if (this.expr == null) {
                this.expr = expr
            } else {
                this.expr = BinaryExpr(this.expr, expr, BinaryExpr.Operator.PLUS)
            }
            return this
        }

        fun addVar(s: String?): ConcatBuilder {
            return concat(NameExpr(s))
        }
    }

    private fun equalFieldsEqualRecords(
        recordDeclaration: RecordDeclaration,
        invariant: JmlClassExprDeclaration
    ): JmlClassExprDeclaration? {
        if (recordDeclaration.parameters.isEmpty()) {
            return null
        }


        invariant.addModifier(PUBLIC)
        invariant.kind = SimpleName("invariant_free")
        invariant.setName(SimpleName("id_means_equals"))
        invariant.invariant =
            recordDeclaration.parameters()
                .map { it.nameAsString }
                .map {
                    BinaryExpr(
                        FieldAccessExpr(NameExpr("a"), it),
                        FieldAccessExpr(NameExpr("b"), it),
                        EQUALS
                    )
                }
                .reduce { acc, expr -> BinaryExpr(acc, expr, AND) }

        return invariant
    }
}
