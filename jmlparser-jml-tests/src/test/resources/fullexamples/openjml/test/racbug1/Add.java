public class Add
{
  //@ public invariant x() + y() > 0;
  private int my_x;
  private int my_y;
  
  //@ requires the_x + the_y > 0;
  //@ assignable \everything;
  //@ ensures x() == the_x && y() == the_y;
  public Add(final int the_x, final int the_y)
  {
    my_x = the_x;
    my_y = the_y;
  }
  
  public /*@ pure @*/ int x() { return my_x; }
  public /*@ pure @*/ int y() { return my_y; }
  
  //@ ensures \result == x() + y() + the_operand;
  public /*@ pure @*/ int sum(final int the_operand)
  {
    return my_x + my_y + the_operand;
  }
  
  public static void main(final String... the_args)
  {
	System.out.println((new Add(10, 20).sum(30)));
  }
}
