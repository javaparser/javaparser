package tmp;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.JavaParser;
import com.github.javaparser.JavaToken;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.visitor.TreeVisitor;

public class Issue1029 {
    public static void main(String[] args) {
        final BodyDeclaration<?> mainMethod = JavaParser.parseBodyDeclaration("int main(){\n" +
                "          return 0;\n" +
                "     }");

        new TreeVisitor() {
            int count = 0;

            @Override
            public void process(Node node) {
                node.getTokenRange().ifPresent(r -> {
                    count++;
                    JavaToken startComment = new JavaToken(GeneratedJavaParserConstants.MULTI_LINE_COMMENT, "/* " + count + " [ */");
                    JavaToken endComment = new JavaToken(GeneratedJavaParserConstants.MULTI_LINE_COMMENT, "/* ] " + count + " */");
                    // Go to the beginning of the node in the token list, and insert the start comment there.
                    r.getBegin().createCursor().insert(startComment);
                    // Go to after the end of the node in the token list, and insert the end comment there.
                    r.getEnd().createCursor().next().insert(endComment);
                    // Update the node's token range to include these comments.
                    // (Otherwise tokenRange.toString misses the first and last comment)
                    r.setBegin(startComment);
                    r.setEnd(endComment);
                });
            }
        }.visitPreOrder(mainMethod);

        // Don't use the pretty printer since that doesn't use the tokens. Just print the tokenlist instead.
        System.out.println(mainMethod.getTokenRange().get().toString());
    }
}
