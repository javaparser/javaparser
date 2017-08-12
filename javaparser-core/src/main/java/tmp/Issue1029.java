package tmp;

import com.github.javaparser.*;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.visitor.TreeVisitor;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import com.github.javaparser.utils.Pair;

import static com.github.javaparser.GeneratedJavaParserConstants.MULTI_LINE_COMMENT;
import static com.github.javaparser.Providers.*;
import static com.github.javaparser.utils.Utils.EOL;

public class Issue1029 {
    public static void main(String[] args) {
//        final BodyDeclaration<?> mainMethod = JavaParser.parseBodyDeclaration("int main(){" + EOL +
//                "          return 0;" + EOL +
//                "     }");

        Pair<ParseResult<BodyDeclaration<?>>, LexicalPreservingPrinter> setup = LexicalPreservingPrinter.setup(ParseStart.CLASS_BODY, provider("int main(){" + EOL +
                "          return 0;" + EOL +
                "     }"));

        ParseResult<BodyDeclaration<?>> parseResult = setup.a;
        LexicalPreservingPrinter printer = setup.b;
        BodyDeclaration<?> mainMethod = parseResult.getResult().get();
        
        new TreeVisitor() {
            int count = 0;

            @Override
            public void process(Node node) {
                node.getTokenRange().ifPresent(r -> {
                    count++;
                    JavaToken startComment = new JavaToken(MULTI_LINE_COMMENT, "/* " + count + " [ */");
                    JavaToken endComment = new JavaToken(MULTI_LINE_COMMENT, "/* ] " + count + " */");
                    // ???
                    // Go to the beginning of the node in the token list, and insert the start comment there.
//                    r.getBegin().createCursor().insert(startComment);
                    // Go to the end of the node in the token list, and insert the end comment after it.
//                    r.getEnd().createCursor().insertAfter(endComment);
//                     Update the node's token range to include these comments.
                    // (Otherwise tokenRange.toString misses the first and last comment)
//                    r.setBegin(startComment);
//                    r.setEnd(endComment);
                });
            }
        }.visitPreOrder(mainMethod);

        System.out.println(printer.print(mainMethod));
    }
}
