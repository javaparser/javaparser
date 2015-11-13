package me.tomassetti.symbolsolver;


import com.github.javaparser.ParseException;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;

import java.io.File;
import java.io.IOException;


/**
 * Created by federico on 21/08/15.
 */
public class ProjectResolver {

    public static void main(String[] args) throws IOException, ParseException {
        File src = new File("/home/federico/repos/javaparser/javaparser-core/src/main/java");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JreTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(new File("/home/federico/repos/javaparser/javaparser-core/target/generated-sources/javacc")));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor();
        sourceFileInfoExtractor.setTypeSolver(combinedTypeSolver);
        sourceFileInfoExtractor.solve(src);
        System.out.println("OK " + sourceFileInfoExtractor.getOk());
        System.out.println("KO " + sourceFileInfoExtractor.getKo());
        System.out.println("UNSUPPORTED " + sourceFileInfoExtractor.getUnsupported());
    }

}
