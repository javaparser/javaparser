package me.tomassetti.symbolsolver;

import java.io.File;

public abstract class AbstractTest {

    protected static File adaptPath(File path) {
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

    protected static String adaptPath(String path) {
        return adaptPath(new File(path)).getPath();
    }
}
