package foo;
import bar.Base;
import qux.CoolName;
public class Derived extends Base implements CoolName {
  private class CoolName extends Base {}
}
