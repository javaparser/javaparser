package box;

import java.util.function.Function;

interface Foo {}

record Box<T>(T value) implements Foo {
  public <U> Box<U> map(Function<T, U> f) {
    return new Box<U>(f.apply(value));
  }
}
