import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;


public class Test {

  public void blah(Collection<String> tagNames) {
    final Set<String> lowerTagNames = new HashSet<String>();
    lowerTagNames.add(new Function<String, String>() {
      @Override //@ pure
      public String apply(String s) {
        return s.toLowerCase();
      }
    }.apply("adsfeasd"));
  }

}