public class Alice {
  //@ ensures \result.equals("lice");
  public String alice() {
    String alice="Alice";
    return alice.substring(1);
  }
  
  //@ ensures \result.equals("lice");
  public String alice2() {
    String alice="Alice";
    return alice.substring(1,5);
  }

}