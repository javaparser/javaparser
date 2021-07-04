package esc;

public class Child extends Parent {
  //@ public invariant value > 0;
  
  private final int my_value; //@ in value;
  //@ public model int value;
  //@ private represents value = my_value;
  
  //@ requires value_1 > 0;
  //@ ensures value == value_1;
  public Child(final int value_0, final int value_1) {
    super(value_0);
    my_value = value_1;
  }
}
