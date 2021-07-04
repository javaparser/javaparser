
public class RowToString {
    
    //@ requires true;
    public static String rowToString(String ja) {
      StringBuilder sb = new StringBuilder();
      for (int i = 0; i < ja.length(); i += 1) {
          if (i > 0) {
              sb.append(',');
          }
          Object object = null;
          if (object != null) {
              String string = object.toString();
              if (string.length() > 0 && (string.indexOf(',') >= 0 ||
                      string.indexOf('\n') >= 0 || string.indexOf('\r') >= 0 ||
                      string.indexOf(0) >= 0 || string.charAt(0) == '"')) {
                  sb.append('"');
                  int length = string.length();
                  for (int j = 0; j < length; j += 1) {
                      char c = string.charAt(j);
                      if (c >= ' ' && c != '"') {
                          sb.append(c);
                      }
                  }
                  sb.append('"');
              } else {
                  sb.append(string);
              }
          }
      }
      sb.append('\n');
      return sb.toString();
      
  }

}