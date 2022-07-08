package com.github.javaparser.symbolsolver;

import com.github.javaparser.resolution.UnsolvedSymbolException;

/**
 * @author Alexander Weigl
 * @version 1 (08.07.22)
 */
public class JavaRefersToJmlException extends UnsolvedSymbolException {
    public JavaRefersToJmlException(String name) {
        super(name);
    }

    public JavaRefersToJmlException(String name, String context) {
        super(name, context);
    }

    public JavaRefersToJmlException(String name, Throwable cause) {
        super(name, cause);
    }

    public JavaRefersToJmlException(String name, String context, Throwable cause) {
        super(name, context, cause);
    }
}
