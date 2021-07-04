import java.io.IOException;
import java.io.Reader;

public class Next {
    

    /*@ spec_public @*/ private long    character;
    /*@ spec_public @*/ private boolean eof;
    /*@ spec_public @*/ private long    index;
    /*@ spec_public @*/ private long    line;
    /*@ spec_public @*/ private char    previous;  
    /*@ spec_public @*/ private Reader  reader;
    /*@ spec_public @*/ private boolean usePrevious;
  
    
    
    //@ requires this.reader != null;
    public char next() throws Exception {
    int c = 0;
    if (this.usePrevious) {
        this.usePrevious = false;
        c = this.previous;
    } else {
        try {
            c = this.reader.read();
         } catch (IOException exception) {
           throw new Exception(exception);
        }

        if (c <= 0) { // End of stream
            this.eof = true;
            c = 0;
        }
    }
    this.index += 1;
    if (this.previous == '\r') {
        this.line += 1;
        this.character = c == '\n' ? 0 : 1;
    } else if (c == '\n') {
        this.line += 1;
        this.character = 0;
    } else {
        this.character += 1;
    }
    this.previous = (char) c;
    return this.previous;
}
}