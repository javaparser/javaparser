import java.util.function.Function;

record Box<T>(T value) {
  public <U> Box<U> map(Function<T, U> f) {
    return new Box<U>(f.apply(value));
  }
}
