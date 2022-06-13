package com.github.jmlparser.stat;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.jmlparser.Main;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import lombok.Getter;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;
import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.22)
 */
public class StatMain {
    private static final Args args = new Args();

    public static void main(String[] argv) throws ParserConfigurationException, TransformerException {
        JCommander cmd = JCommander.newBuilder()
                .programName("jml-stat")
                .addObject(args)
                .build();
        cmd.parse(argv);

        if (args.help) {
            cmd.usage();
            return;
        }

        ParserConfiguration config = new ParserConfiguration();
        config.setProcessJml(true);
        config.setKeepJmlDocs(true);
        for (String activeJmlKey : args.activeJmlKeys) {
            String[] activeJmlKeys = activeJmlKey.split(",");
            config.getJmlKeys().add(Arrays.asList(activeJmlKeys));
        }

        if (args.activeJmlKeys.isEmpty()) {
            //config.getJmlKeys().add(new ArrayList<>());
            config.getJmlKeys().add(Collections.singletonList("key"));
            //config.getJmlKeys().add(Collections.singletonList("openjml"));
        }


        DocumentBuilderFactory builderFactory = DocumentBuilderFactory.newInstance();
        DocumentBuilder builder = builderFactory.newDocumentBuilder();
        Document xmlDocument = builder.newDocument();
        final Element xmlRoot = xmlDocument.createElement("statistics-model");

        Collection<CompilationUnit> nodes = Main.parse(args.files, config);
        final ExpressionCosts costs = new ExpressionCosts();
        for (List<String> key : config.getJmlKeys()) {
            StatVisitor statVisitor = new StatVisitor(xmlDocument, key, costs);
            Element e = xmlDocument.createElement("settings");
            e.setAttribute("keys", "" + key);
            xmlRoot.appendChild(e);
            for (CompilationUnit node : nodes) {
                node.accept(statVisitor, e);
            }
        }

        //Gson gson = new GsonBuilder().setPrettyPrinting().create();
        //System.out.println(gson.toJson(statVisitor.getNewlines()));

        Transformer transformer = TransformerFactory.newInstance().newTransformer();
        transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");
        StreamResult result = new StreamResult(new StringWriter());
        DOMSource source = new DOMSource(xmlRoot);
        transformer.transform(source, result);
        String xmlString = result.getWriter().toString();
        System.out.println(xmlString);
    }

    private static class Args {
        @Parameter
        private List<String> files = new ArrayList<>();

        @Parameter(names = "-k")
        private List<String> activeJmlKeys = new ArrayList<>();

        @Parameter(names = "-h")
        private boolean help = false;


        @Parameter(names = {"-verbose"}, description = "Level of verbosity")
        private Integer verbose = 1;
    }
}
