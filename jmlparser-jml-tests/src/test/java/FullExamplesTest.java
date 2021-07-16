import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (7/2/21)
 */
public class FullExamplesTest {
    private final JavaParser jpb = new JavaParser();

    Set<String> blocked = new HashSet<>();

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
        blocked.add("/openjml/test/anonymousCaptures/Captures.java");
        blocked.add("/openjml/test/datatype/Test.java");
        blocked.add("/openjml/test/escFPcompose/Test.java");
        blocked.add("/openjml/test/gitbug555/Test.java");
    }


    @TestFactory
    public Stream<DynamicTest> createTests() throws IOException {
        File dir = new File("src/test/resources/fullexamples").getAbsoluteFile();
        System.out.format("Folder: %s\n", dir);
        Assumptions.assumeTrue(dir.exists());
        int prefix = dir.toString().length();
        Stream<Path> files = Files.walk(dir.toPath());
        return files
                .filter(it -> it.toString().endsWith(".java"))
                .filter(it -> !blocked.contains(it.toString().substring(prefix)))
                .map(it -> {
                            String name = it.toString().substring(prefix);
                            return DynamicTest.dynamicTest(name, () -> testParse(it));
                        }
                );
    }

    private void testParse(Path p) throws IOException {
        System.out.println(p);
        ParseResult<CompilationUnit> result = jpb.parse(p);
        result.getProblems().forEach(it -> {
            int line = it.getLocation().map(l -> l.getBegin().getRange().map(r -> r.begin.line).orElse(-1)).orElse(-1);
            System.out.format("%s\n\t%s:%d\n\n", it.getMessage(), p.toString(), line);
        });
        Assertions.assertTrue(result.isSuccessful(), "parsing failed");
    }
}
