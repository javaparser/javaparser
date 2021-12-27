package com.github.jml.printer;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.doc.JmlDoc;
import com.github.javaparser.ast.jml.doc.JmlDocDeclaration;
import com.github.javaparser.ast.jml.doc.JmlDocStmt;
import com.github.javaparser.ast.jml.doc.JmlDocType;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.jml.JmlDocSanitizer;
import jdk.nashorn.internal.ir.annotations.Ignore;
import org.junit.jupiter.api.*;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (7/2/21)
 */
@Disabled
public class FullExamplesTest {
    private final JavaParser jpb;
    private final StoreJMLComments storeProcessor = new StoreJMLComments();
    private final ParserConfiguration config;

    {
        config = new ParserConfiguration();
        config.setStoreTokens(true);
        jpb = new JavaParser(config);
    }

    private static final File dir = new File("src/test/resources/fullexamples").getAbsoluteFile();

    Set<String> blocked = new HashSet<>();
    Set<Path> blockedPaths;

    {
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JTextComponent.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/Component.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/BorderLayout.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JScrollPane.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/GridLayout.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/Frame.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JOptionPane.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/Dimension.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JRadioButtonMenuItem.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/Integer.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/Font.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JRadioButton.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/ActionEvent.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JPanel.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/Window.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/ButtonGroup.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JToggleButton.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JLabel.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JComponent.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/PrintStream.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/Container.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/IllegalStateException.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JTextField.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JTextArea.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/AbstractButton.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JFrame.java");
        blocked.add("/key/standard_key/BookExamples/10UsingKeY/Bank-JML/classpath/JButton.java");
        blocked.add("/key/firstTouch/11-StateMerging/A.java");
        blocked.add("/key/firstTouch/11-StateMerging/Gcd.java");
        blocked.add("/key/completionscopes/src/CompletionScopes.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JTextComponent.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/Component.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/BorderLayout.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JScrollPane.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/GridLayout.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/Frame.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JOptionPane.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/Dimension.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JRadioButtonMenuItem.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/Integer.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/Font.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JRadioButton.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/ActionEvent.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JPanel.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/Window.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/ButtonGroup.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JToggleButton.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JLabel.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JComponent.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/PrintStream.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/Container.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/IllegalStateException.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JTextField.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JTextArea.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/AbstractButton.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JFrame.java");
        blocked.add("/key/standard_key/java_dl/payCardJML/classpath/JButton.java");
        blocked.add("/key/completionscopes/src7CompletionScopes.java");
        blocked.add("/key/heap/block_loop_contracts/List/src/IntList.java");
        blocked.add("/key/heap/block_loop_contracts/ListsWithIterators/src/IntList.java");
        blocked.add("/key/heap/block_loop_contracts/List/src/IntLinkedList.java");
        blocked.add("/openjml/test/anonymousCaptures/Captures.java");
        blocked.add("/openjml/test/datatype/Test.java");
        blocked.add("/openjml/test/escFPcompose/Test.java");
        blocked.add("/openjml/test/gitbug555/Test.java");
        blocked.add("/key/standard_key/java_dl/classpath/IllegalStateException.java");
        blocked.add("/key/standard_key/java_dl/classpath/InputStream.java");


        blockedPaths = blocked.stream().map(it -> Paths.get(dir.toString(), it))
                .collect(Collectors.toSet());
    }


    static int prefixLength = dir.toString().length();

    @TestFactory
    public Stream<DynamicTest> createTests() throws IOException {
        //System.out.format("Folder: %s\n", dir);
        Assumptions.assumeTrue(dir.exists());
        Stream<Path> files = Files.walk(dir.toPath());
        return files
                .filter(it -> it.toString().endsWith(".java"))
                //.filter(it -> it.toString().contains("openjml"))
                .filter(it -> !it.toString().contains("InformationFlow"))
                .map(it -> {
                            String name = it.toString().substring(prefixLength);
                            return DynamicTest.dynamicTest(name, () -> testParse(it));
                        }
                );
    }

    private void testParse(Path p) throws IOException {
        Assumptions.assumeFalse(isBlocked(p));
        System.out.println(p);
        ParseResult<CompilationUnit> result = jpb.parse(p);
        result.getProblems().forEach(it -> {
            int line = it.getLocation().map(l -> l.getBegin().getRange().map(r -> r.begin.line).orElse(-1)).orElse(-1);
            System.out.format("%s\n\t%s:%d\n\n", it.getMessage(), p.toUri(), line);
            it.getCause().ifPresent(c -> c.printStackTrace());
        });
        //storeProcessor.process(result, config);
        Assertions.assertTrue(result.isSuccessful(), "parsing failed");
    }

    private boolean isBlocked(Path it) {
        return blockedPaths.contains(it);
    }


}

class StoreJMLComments implements ParseResult.PostProcessor {
    private final JmlDocSanitizer sanitizer = new JmlDocSanitizer(new TreeSet<>());
    private String origin;

    @Override
    public void process(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        if (result.getResult().isPresent()) {
            final Node node = result.getResult().get();
            if (node instanceof CompilationUnit) {
                origin = ((CompilationUnit) node).getStorage()
                        .map(it -> it.getPath().toFile().toString()).orElse("no path given");
            } else {
                origin = "n/a";
            }
            node.accept(new Visitor(), null);
        }
    }

    private void write(String cat, NodeList<JmlDoc> comment) {
        if (comment.isEmpty()) return;

        Path f = Paths.get("src", "test", "resources", "fragments",
                cat + "_" + Math.abs(comment.hashCode()) + ".txt");
        String s = sanitizer.asString(comment);
        String pos = comment.get(0).getRange().map(it -> it.begin.toString()).orElse("");
        try (FileWriter fw = new FileWriter(f.toFile())) {
            fw.write("// Origin: " + origin + "@" + pos + "\n");
            fw.write(s.trim());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    class Visitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(JmlDocType n, Void arg) {
            write("type", n.getJmlComments());
        }

        @Override
        public void visit(JmlDocDeclaration n, Void arg) {
            write("decl", n.getJmlComments());
        }

        @Override
        public void visit(JmlDocStmt n, Void arg) {
            write("stmt", n.getJmlComments());
        }
    }
}