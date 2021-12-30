import com.github.javaparser.JavaParser
import com.github.javaparser.JavaParserBuild
import com.github.javaparser.ParserConfiguration
import com.github.javaparser.ast.Jmlish
import com.github.javaparser.ast.Node
import com.github.javaparser.metamodel.NodeMetaModel
import com.github.javaparser.metamodel.PropertyMetaModel
import com.github.javaparser.printer.DefaultPrettyPrinter
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration
import io.ktor.application.*
import io.ktor.features.*
import io.ktor.html.*
import io.ktor.http.*
import io.ktor.http.content.*
import io.ktor.request.*
import io.ktor.routing.*
import io.ktor.server.engine.*
import io.ktor.server.netty.*
import io.ktor.util.pipeline.*
import kotlinx.html.*
import java.io.StringReader
import java.util.stream.Collectors

const val version = "${JavaParserBuild.PROJECT_VERSION} (${JavaParserBuild.MAVEN_BUILD_TIMESTAMP})"

fun main() {
    embeddedServer(Netty, port = 8000, watchPaths = listOf("classes", "resources")) {
        install(StatusPages)
        routing {
            get("/") { renderPage() }
            post("parse") {
                val params = call.receiveParameters()
                renderPage(params)
            }

            static("assets") {
                resources("assets")
            }
        }
    }.start(wait = true)
}

private suspend fun PipelineContext<Unit, ApplicationCall>.renderPage(params: Parameters? = null) {
    val inputText = params?.get("input")
    val keyKey = params?.get("keyKey")
    val keyOpenJml = params?.get("keyOpenJml")
    val keyESC = params?.get("keyESC")
    val keyRAC = params?.get("keyRAC")
    val doNotProcessJml = params?.get("doNotProcessJml") != null

    call.respondHtmlTemplate(DefaultPage()) {
        body {
            div("form-group") {
                form(action = "/parse", method = FormMethod.post) {
                    div {
                        spectreCheckBox(name = "doNotProcessJml") { +"Do not process JML" }
                        span { +" Active keys: " }
                        spectreCheckBox(name = "keyKey") { +"KEY" }
                        spectreCheckBox(name = "keyOpenJml") { +"OpenJml" }
                        spectreCheckBox(name = "keyESC") { +"ESC" }
                        spectreCheckBox(name = "keyRAC") { +"RAC" }
                        submitInput(classes = "btn btn-primary") { }
                    }
                    textArea {
                        name = "input"
                        id = "input"
                        rows = "100"
                        cols = "120"
                        if (inputText != null) {
                            +inputText
                        } else {
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
        right {
            if (inputText != null) {
                val config = ParserConfiguration()

                config.isProcessJml = !doNotProcessJml

                if (keyKey != null) {
                    config.jmlKeys.add("key")
                }
                if (keyESC != null) {
                    config.jmlKeys.add("openjml")
                }
                if (keyOpenJml != null) {
                    config.jmlKeys.add("ESC")
                }
                if (keyRAC != null) {
                    config.jmlKeys.add("RAC")
                }

                val jpb = JavaParser(config)

                val startTime = System.nanoTime()
                val result = jpb.parse(StringReader(inputText))
                val stopTime = System.nanoTime()
                val durationNano = stopTime - startTime



                accordion("Processing Information") {
                    ul {
                        li { +"Activated keys: ${config.jmlKeys}" }
                        li { +"Parsing took: ${durationNano / 1000.0 / 1000.0} ms     " }
                        li { if (result.isSuccessful) +"Parsing was successful" else +"Parsing has errors" }
                    }
                }

                accordion("Parse Issues", isOpen = true) {
                    if (!result.isSuccessful) {
                        code {
                            pre {
                                result.problems.forEach {
                                    +it.toString()
                                }
                            }
                        }
                    } else {
                        +"No issues detected"
                    }
                }

                result.result.ifPresent {
                    val c = DefaultPrinterConfiguration()
                    val v = DefaultPrettyPrinter(c)
                    val pp = v.print(it)
                    accordion("Pretty Printed") {
                        code { pre { +pp } }
                    }
                }

                accordion("AST", isOpen = true) {
                    val cu = result.result.get()
                    ul("ast") {
                        this.printNode(cu, "[0]")
                    }
                }

                /*accordion("Original sources") {
                    textArea {
                        name = "input"
                        id = "input"
                        rows = "100"
                        cols = "120"
                        +inputText
                    }
                    //code { pre { +inputText } }
                }*/
            }
        }
    }
}


@HtmlTagMarker
inline fun FlowContent.accordion(
    title: String = "", icon: String = "", isOpen: Boolean = false,
    crossinline block: DIV.() -> Unit
) {
    details("accordion") {
        open = isOpen
        summary("accordion-header") {
            i(classes = "icon icon-arrow-right mr-1 " + icon) {}
            +title
        }
        div("accordion-body") {
            block(this)
        }
    }
}

@HtmlTagMarker
inline fun FlowOrInteractiveOrPhrasingContent.spectreCheckBox(
    name: String? = null, label: String = "", crossinline block: INPUT.() -> Unit
) {
    label("form-checkbox d-inline-block") {
        input(type = InputType.checkBox, name = name) { block(this) }
        i("form-icon") { +label }
    }
}


open class DefaultPage : Template<HTML> {
    val body = Placeholder<FlowContent>()
    val right = Placeholder<FlowContent>()
    val top = Placeholder<FlowContent>()

    override fun HTML.apply() {
        head {
            title("JmlParser -- Playground")

            styleLink("/assets/spectre.min.css")
            //styleLink("/assets/spectre-exp.min.css")
            styleLink("/assets/spectre-icons.min.css")
            styleLink("/assets/style.css")

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
                +"JmlParser — Playground"
                span("version label label-rounded label-secondary") {
                    +version
                }
            }

            div("inner") {
                div("container") {
                    div("column col-12") { insert(top) }
                }
                div("container") {
                    div("columns") {
                        div("column col-5") { insert(body) }
                        div("divider-vert") { attributes["data-content"] = "&mid;" }
                        div("column col-5") { insert(right) }
                    }

                }

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

private fun UL.printNode(n: Node, text: String = "") {
    val isJml = n is Jmlish
    val clazz = if (isJml) "jmlish" else ""

    li(clazz) {
        span("attrib-name") { +text }
        +": "
        span("type-name") { +n.metaModel.typeName }

        n.range.ifPresent {
            span("range") {
                +"${it.begin.line}/${it.begin.column} - ${it.end.line}/${it.end.column}"
            }
        }

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
                    span("value") {
                        attributeMetaModel.getValue(n)?.let { +it.toString() }
                    }
                }
            }

            for (subNodeMetaModel in subNodes) {
                val value = subNodeMetaModel.getValue(n) as Node?
                if (value != null) {
                    printNode(value, subNodeMetaModel.name)
                }
            }

            for (subListMetaModel in subLists) {
                val subList = subListMetaModel.getValue(n) as com.github.javaparser.ast.NodeList<out Node>
                if (!subList.isEmpty()) {
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
