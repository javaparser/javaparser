import java.io.Reader;
import java.io.Reader;

public class GetValue {

    /* @ spec_public @ */ private long character;
    /* @ spec_public @ */ private boolean eof;
    /* @ spec_public @ */ private long index;
    /* @ spec_public @ */ private long line;
    /* @ spec_public @ */ private char previous;
    /* @ spec_public @ */ private Reader reader;
    /* @ spec_public @ */ private boolean usePrevious;

    // @ requires x != null;
    private static String getValue(Reader x) throws Exception {
	char c;
	char q;
	
	StringBuffer sb = new StringBuffer(); 
	do {
	    c = (char)x.read();
	} while (c == ' ' || c == '\t');
	switch (c) {
	case 0:
	    return null;
	case '"':
	case '\'':
	    q = c;
	    sb = new StringBuffer();
	    for (;;) {
		c = (char)x.read();
		if (c == q) {
		    // Handle escaped double-quote
		    if ((char)x.read() != '\"') {
			//x.back();
			break;
		    }
		}
		if (c == 0 || c == '\n' || c == '\r') {
		    //throw x.syntaxError("Missing close quote '" + q + "'.");
		}
		sb.append(c);
	    }
	    return sb.toString();
	case ',':
	    //x.back();
	    return "";
	default:
	    //x.back();
	    return sb.toString();
	}
    }
}