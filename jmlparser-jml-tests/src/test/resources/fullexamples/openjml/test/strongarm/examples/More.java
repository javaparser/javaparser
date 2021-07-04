import java.io.Reader;

public class More {
    

    /*@ spec_public @*/ private long    character;
    /*@ spec_public @*/ private boolean eof;
    /*@ spec_public @*/ private long    index;
    /*@ spec_public @*/ private long    line;
    /*@ spec_public @*/ private char    previous;  
    /*@ spec_public @*/ private Reader  reader;
    /*@ spec_public @*/ private boolean usePrevious;
  
    
    
    //@ requires true;
    //@ ensures \result == (eof && !usePrevious);
    public  boolean end() {
	return this.eof && !this.usePrevious;
    }
    
    
    
    //@ requires this.reader != null;
    public boolean more() throws Exception {
        if (this.end()) {
            return false;
        }
        return true;
    }


}