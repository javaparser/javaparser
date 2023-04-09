package com.github.jmlparser.redux;

import java.util.HashSet;
import java.util.Set;

/**
 * Configuration for the Redux transformation pipeline.
 */
public class ReduxConfig {
    private Set<String> disabled = new HashSet<>();

    public void enable(Class<?> clazz) {
        disabled.remove(clazz.toString());
    }

    public void disable(Class<?> clazz) {
        disabled.add(clazz.toString());
    }

    public Set<String> getDisabled() {
        return disabled;
    }

    public boolean isEnabled(String clazz) {
        return !disabled.contains(clazz);
    }
}