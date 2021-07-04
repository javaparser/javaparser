public class Counter {
  int value;

  //@ ensures this.value == v;
  Counter(int v)
  {
    this.value=v;
  }
  
  //@ ensures v.value == \old(v.value) && this.value == \old(v.value);
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
