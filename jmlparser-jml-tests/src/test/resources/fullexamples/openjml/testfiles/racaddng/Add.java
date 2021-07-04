public class Add
{
  //@ public invariant x() + y() > 0;
  
  private /*@ spec_public */ int my_x;
  private /*@ spec_public */ int my_y;
  
  //@ requires the_x + the_y > 0;
  //@ ensures x() == the_x && y() == the_y;
  public Add(final int the_x, final int the_y)
  {
    my_x = the_x;
    my_y = the_y;
  }
  
  //@ ensures \result == my_x;
  public /*@ pure helper @*/ int x() { return my_x; }
  //@ ensures \result == my_y;
  public /*@ pure helper @*/ int y() { return my_y; }
  
  //@ ensures \result == x() + y() + the_operand;
  public /*@ pure @*/ int sum(final int the_operand)
  {
    return my_x + my_y + the_operand;
  }
}
