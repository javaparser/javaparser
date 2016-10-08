package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import me.tomassetti.symbolsolver.SourceFileInfoExtractor;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * We analize a more recent version of JavaParser, after the project moved to Java 8.
 */
public class AnalyseNewJavaParserTest {

    private static final File src = adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-core"));

    private static File adaptPath(File path) {
        if (path.exists()) {
            return path;
        } else {
            File underJavaParserCore = new File("java-symbol-solver-core/" + path.getPath());
            if (underJavaParserCore.exists()) {
                return underJavaParserCore;
            } else {
                throw new IllegalArgumentException();
            }
        }
    }

    private static SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JreTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-generated-sources"))));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor();
        sourceFileInfoExtractor.setTypeSolver(combinedTypeSolver);
        sourceFileInfoExtractor.setPrintFileName(false);
        return sourceFileInfoExtractor;
    }

    private static SourceFileInfoExtractor sourceFileInfoExtractor = getSourceFileInfoExtractor();

    static String readFile(File file)
            throws IOException
    {
        byte[] encoded = Files.readAllBytes(Paths.get(file.getAbsolutePath()));
        return new String(encoded, StandardCharsets.UTF_8);
    }

    private static final boolean DEBUG = true;

    private void parse(String fileName) throws IOException, ParseException {
        File sourceFile = new File(src.getAbsolutePath() + "/" + fileName + ".java");
        OutputStream outErrStream = new ByteArrayOutputStream();
        PrintStream outErr = new PrintStream(outErrStream);

        sourceFileInfoExtractor.setOut(outErr);
        sourceFileInfoExtractor.setErr(outErr);
        sourceFileInfoExtractor.solveMethodCalls(sourceFile);
        String output = outErrStream.toString();

        String path = adaptPath(new File("src/test/resources/javaparser_methodcalls_expected_output")).getPath()+ "/" + fileName.replaceAll("/", "_")+ ".txt";
        File dstFile = new File(path);

        if (DEBUG && (sourceFileInfoExtractor.getKo() != 0 || sourceFileInfoExtractor.getUnsupported() != 0)){
            System.err.println(output);
        }

        assertTrue("No failures expected when analyzing " + path, 0 == sourceFileInfoExtractor.getKo());
        assertTrue("No UnsupportedOperationException expected when analyzing " + path, 0 == sourceFileInfoExtractor.getUnsupported());

        String expected = readFile(dstFile);

        String[] outputLines = output.split("\n");
        String[] expectedLines = expected.split("\n");

        for (int i=0; i<Math.min(outputLines.length, expectedLines.length); i++) {
            assertEquals("Line " + (i+1) + " of " + path + " is different from what is expected", expectedLines[i].trim(), outputLines[i].trim());
        }

        assertEquals(expectedLines.length, outputLines.length);
        
        JavaParserFacade.clearInstances();

        // If we need to update the file uncomment these lines
        //PrintWriter writer = new PrintWriter(dstFile.getAbsoluteFile(), "UTF-8");
        //writer.print(output);
        //writer.close();
    }

    @Test
    public void parsePositionUtils() throws IOException, ParseException {
        parse("com/github/javaparser/CommentsInserter");
    }


}
