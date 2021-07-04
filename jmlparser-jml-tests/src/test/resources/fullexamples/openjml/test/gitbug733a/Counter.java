public class Counter {
  int value;

  //@ ensures this.value == v;
  Counter(int v)
  {
    this.value=v;
  }
  
  //@ ensures this != v && this.value == v.value;
  //@ pure
  Counter(Counter v)
  {
    this.value=v.value;
  }

  public static void main(String[] args)
  {
    Counter c1 = new Counter(3);
    Counter c2= new Counter(c1);
    //@ assert c1.value == c2.value;
  }
}
