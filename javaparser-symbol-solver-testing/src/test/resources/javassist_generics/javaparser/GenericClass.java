package javaparser;

import java.util.List;
import java.util.Map;

public class GenericClass<S> {

    public S get() {
        return null;
    }

    public <T> List<List<T>> genericMethodWithNestedReturnType() {
        return null;
    }

    public <T,V> Map<T,V> genericMethodWithDoubleTypedReturnType() {
        return null;
    }

    public static <T> GenericClass<T> copy(GenericClass<T> input) {
        return null;
    }

    public static <T extends Object & Foo<? extends T>> T complexGenerics() {
        return null;
    }

    public static <T> List<T> asList(T element) {
        return null;
    }

    public interface Foo<T> {
    }

    public interface Bar {
        public static List<NestedBar> CONSTANT = null;

        public interface NestedBar {
        }
    }

}
