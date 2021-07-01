import io.ktor.application.*
import io.ktor.html.*
import io.ktor.request.*
import io.ktor.routing.*
import io.ktor.server.engine.*
import io.ktor.server.netty.*
import kotlinx.html.*

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
                                rows = "50"
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

                call.respondHtmlTemplate(DefaultPage()) {
                    body {
                        div {
                            h2 { +"Pretty Printed" }
                            code { pre { +inputText } }
                        }
                        div {
                            h2 { +"Parse Issues" }
                            code { pre { +inputText } }
                        }
                        div {
                            h2 { +"AST" }
                            code { pre { +inputText } }
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

open class DefaultPage : Template<HTML> {
    val body = Placeholder<FlowContent>()

    override fun HTML.apply() {
        head {
            title("JmlParser -- Playground")
            link("style.css", "stylesheet")
        }
        body {
            div("content")
            h1 { +"JmlParser -- Playground" }
            div("inner") {
                insert(body)
            }
        }
    }
}
