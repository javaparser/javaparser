public class Sanitize {

    // private static String[] exceptions = {"em", "strong", "h1"}; 

    /*@ public normal_behavior 
      @ ensures \result.indexOf('<') == -1 && \result.indexOf('>') == -1;
      @*/
    public static String simpleSanitize(String s) {
	return s.replace('<', '[').replace('>',']');
    }


}