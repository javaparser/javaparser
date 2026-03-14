package io.github.jmltoolkit.cli

import com.github.ajalt.clikt.core.Context
import com.github.javaparser.ParserConfiguration
import io.github.jmltoolkit.stat.ExpressionCosts
import io.github.jmltoolkit.stat.StatVisitor
import java.io.StringWriter
import javax.xml.parsers.DocumentBuilderFactory
import javax.xml.transform.OutputKeys
import javax.xml.transform.TransformerFactory
import javax.xml.transform.dom.DOMSource
import javax.xml.transform.stream.StreamResult

/**
 * @author Alexander Weigl
 * @version 1 (24.05.22)
 */
class StatMain : FileBasedCommand("stat") {
    override fun help(context: Context): String = "Statistics for JML specification"

    override fun run() {
        val config = ParserConfiguration()
        config.setProcessJml(true)
        config.setKeepJmlDocs(true)
        for (activeJmlKey in activeJmlKeys) {
            val activeJmlKeys = activeJmlKey.split(",".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
            config.jmlKeys.add(listOf(*activeJmlKeys))
        }

        if (activeJmlKeys.isEmpty()) {
            //config.getJmlKeys().add(new ArrayList<>());
            config.jmlKeys.add(listOf("key"))
            //config.getJmlKeys().add(Collections.singletonList("openjml"));
        }


        val builderFactory = DocumentBuilderFactory.newInstance()
        val builder = builderFactory.newDocumentBuilder()
        val xmlDocument = builder.newDocument()
        val xmlRoot = xmlDocument.createElement("statistics-model")

        val nodes = parse(files, config)
        val costs = ExpressionCosts()
        for (key in config.jmlKeys) {
            val statVisitor = StatVisitor(xmlDocument, key, costs)
            val e = xmlDocument.createElement("settings")
            e.setAttribute("keys", "" + key)
            xmlRoot.appendChild(e)
            for (node in nodes) {
                node.accept(statVisitor, e)
            }
        }

        //Gson gson = new GsonBuilder().setPrettyPrinting().create();
        //System.out.println(gson.toJson(statVisitor.getNewlines()));
        val transformer = TransformerFactory.newInstance().newTransformer()
        transformer.setOutputProperty(OutputKeys.INDENT, "yes")
        transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2")
        val result = StreamResult(StringWriter())
        val source = DOMSource(xmlRoot)
        transformer.transform(source, result)
        val xmlString = result.writer.toString()
        println(xmlString)
    }

    //val files by argument("FILES")
    //val activeJmlKeys: List<String> by option("-k").multiple()
}
