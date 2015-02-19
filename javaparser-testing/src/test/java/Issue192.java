import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

/**
 * Created by federico on 03/09/15.
 */
public class Issue192 {

    public static void main(String[] args) throws ParseException {
        String code = "public class StepImplementation {\n" +
                "    public void contextStep() {\n" +
                "        for (int i = 0; i < 5; i++) {\n" +
                "            // foo bar\n" +
                "            System.out.println();\n" +
                "            // another foo bar\n" +
                "        }\n" +
                "    }\n" +
                "}";
        InputStream stream = new ByteArrayInputStream(code.getBytes(StandardCharsets.UTF_8));
        CompilationUnit cu = JavaParser.parse(stream);
        lookInto(cu);
    }

    private static void lookInto(Node node) {
        if (node.getOrphanComments() != null && node.getOrphanComments().size() > 0) {
            System.out.println("GOTCHA in " + node.getClass().getCanonicalName());
        }
        for (Node child : node.getChildrenNodes()) {
            lookInto(child);
        }
    }

}
