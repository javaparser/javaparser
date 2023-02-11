package com.github.jmlparser.redux;

import java.util.HashSet;
import java.util.Set;

/**
 * Configuration for the Redux transformation pipeline.
 */
public class ReduxConfig {
    private Set<Class<?>> disabled = new HashSet<>();

    public void enable(Class<?> clazz) {
        disabled.remove(clazz);
    }

    public void disable(Class<?> clazz) {
        disabled.add(clazz);
    }
}