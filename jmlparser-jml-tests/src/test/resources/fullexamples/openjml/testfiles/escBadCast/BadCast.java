// From DMZ - 10/16/2013

public class BadCast {
    public int my_dollars;
    public int my_cents;
    
    public boolean equals(final Object the_other) {
        boolean result = false;
        
        if (this == the_other) {
          result = true;
        } else if (the_other != null && the_other.getClass() == getClass()) {
          final BadCast other_cash = (BadCast) the_other;
          result = other_cash.my_dollars == my_dollars && 
                   other_cash.my_cents == my_cents;
        }
        
        return result;
      }
}

class BadCast2 {
    public int my_dollars;
    public int my_cents;

    public boolean equals(final Object the_other) {
        boolean result = false;
        
        if (this == the_other) {
          result = true;
        } else if (the_other != null && the_other instanceof BadCast2) {
          final BadCast2 other_cash = (BadCast2) the_other;
          result = other_cash.my_dollars == my_dollars && 
                   other_cash.my_cents == my_cents;
        }
        
        return result;
      }
}