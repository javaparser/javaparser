package com.github.javaparser.model;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class Flags {
    private final Set<Object> flags = new HashSet<>();

    public void set(Object... flags) {
        Collections.addAll(this.flags, flags);
    }

    public boolean isSet(Object flag) {
        return flags.contains(flag);
    }

    public void unset(Object flag) {
        flags.remove(flag);
    }
}
