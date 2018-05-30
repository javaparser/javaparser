package com.github.javaparser;

import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;

public class AutoCloseableStreamProvider extends StreamProvider implements AutoCloseableProvider {
    public AutoCloseableStreamProvider(Reader reader) {
        super(reader);
    }

    public AutoCloseableStreamProvider(InputStream stream) throws IOException {
        super(stream);
    }

    public AutoCloseableStreamProvider(InputStream stream, String charsetName) throws IOException {
        super(stream, charsetName);
    }
}
