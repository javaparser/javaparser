package com.github.javaparser;

import java.util.Collection;

public class BoundsTest {

    public static <T extends Object & Foo<? super T>> T min(Collection<? extends T> coll) {
        return null;
    }

    public interface Foo<T> {
    }
}
