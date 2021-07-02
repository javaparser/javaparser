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
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (7/2/21)
 */
public class FullExamplesTest {
    private JavaParser jpb = new JavaParser();

    @TestFactory
    public Stream<DynamicTest> createTests() throws IOException {
        File dir = new File("src/test/resources/fullexamples").getAbsoluteFile();
        System.out.format("Folder: %s\n", dir);
        Assumptions.assumeTrue(dir.exists());
        int prefix = dir.toString().length();
        Stream<Path> files = Files.walk(dir.toPath());
        return files
                .filter(it -> it.toString().endsWith(".java"))
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
