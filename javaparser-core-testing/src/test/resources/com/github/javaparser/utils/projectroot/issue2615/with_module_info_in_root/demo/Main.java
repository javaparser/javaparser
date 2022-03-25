package demo;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.ParserCollectionStrategy;
import com.github.javaparser.utils.ProjectRoot;
import com.github.javaparser.utils.SourceRoot;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

/* If there is a module declaration in the root directory, JavaParser doesn't find any .java files. */
public class Main {

    public static void main(String[] args) {
        if (args.length < 1) {
            System.err.println("Usage: provide one or more directory names to process");
            System.exit(1);
        }
        for (String dir : args) {
            process(dir);
        }
    }

    private static void process(String dir) {
        Path root = Paths.get(dir);
        Callback cb = new Callback();
        ProjectRoot projectRoot = new ParserCollectionStrategy().collect(root);
        projectRoot.getSourceRoots().forEach(sourceRoot -> {
            try {
                sourceRoot.parse("", cb);
            } catch (IOException e) {
                System.err.println("IOException: " + e);
            }
        });
    }

    private static class Callback implements SourceRoot.Callback {

        @Override
        public Result process(Path localPath, Path absolutePath, ParseResult<CompilationUnit> result) {
            System.out.printf("Found %s%n", absolutePath);
            return Result.SAVE;
        }
    }
}
