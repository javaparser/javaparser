import java.io.Reader;

public class End {
    
    /*@ spec_public @*/ private long    character;
    /*@ spec_public @*/ private boolean eof;
    /*@ spec_public @*/ private long    index;
    /*@ spec_public @*/ private long    line;
    /*@ spec_public @*/ private char    previous;  
    /*@ spec_public @*/ private Reader  reader;
    /*@ spec_public @*/ private boolean usePrevious;
  

    
    
    
    
    //@ requires true;
    public  boolean end() {
	return this.eof && !this.usePrevious;
    }
}