import com.github.javaparser.JavaParser
import com.github.javaparser.JavaParserBuild
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import com.github.javaparser.metamodel.NodeMetaModel
import com.github.javaparser.metamodel.PropertyMetaModel
import com.github.javaparser.printer.DefaultPrettyPrinter
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration
import io.ktor.application.*
import io.ktor.html.*
import io.ktor.request.*
import io.ktor.routing.*
import io.ktor.server.engine.*
import io.ktor.server.netty.*
import kotlinx.html.*
import java.io.StringReader
import java.util.stream.Collectors

const val version = "${JavaParserBuild.PROJECT_VERSION} (${JavaParserBuild.MAVEN_BUILD_TIMESTAMP})"

fun main() {
    embeddedServer(Netty, port = 8000) {
        routing {
            get("/") {
                call.respondHtmlTemplate(DefaultPage()) {
                    body {
                        form(action = "/parse", method = FormMethod.post) {
                            submitInput { }
                            br {}
                            textArea {
                                name = "input"
                                id = "input"
                                rows = "100"
                                cols = "120"
                                +"""
                                    public class JmlTest {
                                        /*@
                                            requires true;
                                            ensures true;
                                            assignable \strictly_nothing;
                                        */
                                        public void foo() {
                                        
                                        }
                                    }
                                """.trimIndent()
                            }

                        }
                    }
                }
            }

            post("parse") {
                val params = call.receiveParameters()
                val inputText = params["input"]?.toString() ?: "/* empty */"

                val jpb = JavaParser()

                val startTime = System.nanoTime()
                val result = jpb.parse(StringReader(inputText))
                val stopTime = System.nanoTime()
                val durationNano = stopTime - startTime

                call.respondHtmlTemplate(DefaultPage()) {
                    body {
                        div("") {
                            +"Parsing took: ${durationNano / 1000.0 / 1000.0} ms     "
                        }
                        if (result.isSuccessful) {
                            div("success") {
                                +"Parsing was successful"
                            }
                        } else {
                            div("issues") {
                                h2 { +"Parse Issues" }
                                code {
                                    pre {
                                        result.problems.forEach {
                                            +it.toString()
                                        }
                                    }
                                }
                            }
                        }

                        result.result.ifPresent {
                            val c = DefaultPrinterConfiguration()
                            val v = DefaultPrettyPrinter(c)
                            val pp = v.print(it)
                            div {
                                h2 { +"Pretty Printed" }
                                code { pre { +pp } }
                            }
                        }

                        div("ast") {
                            h2 { +"AST" }
                            val cu = result.result.get()
                            ul {
                                this.printNode(cu, "[0]")
                            }
                        }
                        div {
                            h2 { +"Original sources" }
                            code { pre { +inputText } }
                        }
                    }
                }
            }
        }
    }.start(wait = true)
}

private fun UL.printNode(n: Node, text: String = "") {
    li {
        span("attrib-name") { +text }
        +": "
        span("type-name") { +n.metaModel.typeName }
        ul {
            val metaModel: NodeMetaModel = n.metaModel
            val allPropertyMetaModels = metaModel.allPropertyMetaModels
            val attributes = allPropertyMetaModels.stream().filter { obj: PropertyMetaModel -> obj.isAttribute }
                .filter { obj: PropertyMetaModel -> obj.isSingular }
                .collect(Collectors.toList())
            val subNodes = allPropertyMetaModels.stream().filter { obj: PropertyMetaModel -> obj.isNode }
                .filter { obj: PropertyMetaModel -> obj.isSingular }
                .collect(Collectors.toList())
            val subLists = allPropertyMetaModels.stream().filter { obj: PropertyMetaModel -> obj.isNodeList }
                .collect(Collectors.toList())

            for (attributeMetaModel in attributes) {
                li {
                    span("attrib-name") { +attributeMetaModel.name }
                    +": "
                    span("type-name") { +attributeMetaModel.typeName }
                    +" = "
                    span("value") { +attributeMetaModel.getValue(n).toString() }
                }
            }

            for (subNodeMetaModel in subNodes) {
                val value = subNodeMetaModel.getValue(n) as Node?
                if (value != null) {
                    printNode(value, subNodeMetaModel.name)
                }
            }

            for (subListMetaModel in subLists) {
                val subList = subListMetaModel.getValue(n) as NodeList<out Node>?
                if (subList != null && !subList.isEmpty()) {
                    val listName = subListMetaModel.name
                    li {
                        span("attrib-name") { +listName }
                        +": "
                        span("type-name") { +subListMetaModel.typeName }
                        ul {
                            subList.forEachIndexed { idx, it ->
                                printNode(it, "[$idx]")
                            }
                        }
                    }

                }
            }
        }
    }
}

const val STYLE = """
.version { font-size: 80%; margin:1em;}

.ast {
    font-family: monospace;
}

.ast li {
    line-height: 180%;
}

.value {
    background: rgb(133 88 255 / 30%);
    border: 1px solid rgb(133 88 255 / 80%);
    border-radius: 2px;
    padding: .1ex;
}

.type-name {    
    background: rgb(109 248 46 / 30%);
    border: 1px solid rgb(109 248 46 / 80%);
    border-radius: 2px;
    padding: .1ex;
}

.attrib-name {
    background: rgb(251 78 251 / 30%);
    border: 1px solid rgb(251 78 251 / 80%);
    border-radius: 2px;
    padding: .1ex;
} 
"""

open class DefaultPage : Template<HTML> {
    val body = Placeholder<FlowContent>()

    override fun HTML.apply() {
        head {
            title("JmlParser -- Playground")
            style { +STYLE }

            script { src = "https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.32.0/codemirror.min.js" }
            script { src = "https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.62.0/mode/clike/clike.min.js" }

            link {
                rel = "stylesheet"
                href = "https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.32.0/codemirror.min.css"
            }
        }
        body {
            div("content")
            h1 {
                +"JmlParser -- Playground"
                span("version") {
                    +version
                }
            }

            div("inner") {
                insert(body)
            }
            script {
                unsafe {
                    +("var editor = CodeMirror.fromTextArea(document.getElementById('input'), " +
                            "{ lineNumbers: true, mode: \"text/x-java\", matchBrackets: true });" +
                            "editor.setSize(\"100%\", \"90%\");\n")
                }
            }
        }
    }
}
