public enum TableMovieKeys {
        CREATE("CREATE TABLE movie_keys (id TEXT PRIMARY KEY NOT NULL, decryption_key TEXT NOT NULL)"),
        KEY_MOVIE("id"),
        KEY_DECRYPTION_KEY("decryption_key"),
        NAME("movie_keys");
         private /*@ spec_public @*/ String value;

 

     //@ requires str!=null;

     //@ ensures value == str; // should this be value.equals(str)?

     //@ assignable value;

      TableMovieKeys(String str){

            this.value = str;

      }
 

     //@ensures \result == value; // likewise, should this be .equals?
     public /*@ pure @*/ String get(){return value;} // <<< this is the line that generates the error.

}