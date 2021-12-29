import java.util.Objects;

class A {
    private final int test;

    public A() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        Predicate<Integer> tester = (a) -> a > 10;
        tester.test(outer);
    }


    @FunctionalInterface
    public interface Predicate<T> {
        boolean test(T var1);

        default Predicate<T> and(Predicate<? super T> var1) {
            Objects.requireNonNull(var1);
            return (var2) -> {
                return this.test(var2) && var1.test(var2);
            };
        }

        default Predicate<T> negate() {
            return (var1) -> {
                return !this.test(var1);
            };
        }

        default Predicate<T> or(Predicate<? super T> var1) {
            Objects.requireNonNull(var1);
            return (var2) -> {
                return this.test(var2) || var1.test(var2);
            };
        }

        static <T> Predicate<T> isEqual(Object var0) {
            return null == var0 ? Objects::isNull : (var1) -> {
                return var0.equals(var1);
            };
        }

    }

}
