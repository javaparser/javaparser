import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.Providers;
import com.github.javaparser.ast.jml.ArbitraryNodeContainer;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Arrays;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/21)
 */
public class FragmentTest {
    @TestFactory
    public Stream<DynamicTest> testStatementLevel() {
        return files()
                .filter(it -> it.getName().startsWith("stmt"))
                .map(it -> DynamicTest.dynamicTest(it.getName(), () -> testStatementLevel(it)));
    }

    private void testStatementLevel(File f) throws FileNotFoundException {
        JavaParser jp = new JavaParser();
        ParseResult<ArbitraryNodeContainer> r = jp.parseJmlMethodLevel(Providers.provider(f));
        r.getProblems().forEach(
                it -> System.out.println(it)
        );
        Assertions.assertTrue(r.isSuccessful());
    }

    @TestFactory
    public Stream<DynamicTest> testClassLevel() {
        return files()
                .filter(it -> it.getName().startsWith("decl"))
                .map(it -> DynamicTest.dynamicTest(it.getName(), () -> testClassLevel(it)));
    }

    private void testClassLevel(File f) throws FileNotFoundException {
        JavaParser jp = new JavaParser();
        ParseResult<ArbitraryNodeContainer> r = jp.parseJmlClassLevel(Providers.provider(f));
        r.getProblems().forEach(
                it -> System.out.println(it)
        );
        Assertions.assertTrue(r.isSuccessful());
    }


    private Stream<File> files() {
        File[] files = new File("src/test/resources/fragments").listFiles();
        assert files != null;
        Arrays.sort(files);
        return Arrays.stream(files);
    }
}
