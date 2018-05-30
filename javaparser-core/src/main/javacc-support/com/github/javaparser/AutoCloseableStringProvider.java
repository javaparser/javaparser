package com.github.javaparser;

public class AutoCloseableStringProvider extends StringProvider implements AutoCloseableProvider {
    public AutoCloseableStringProvider(String string) {
        super(string);
    }
}
