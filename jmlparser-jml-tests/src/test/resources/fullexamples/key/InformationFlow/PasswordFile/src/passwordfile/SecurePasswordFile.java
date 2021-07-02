// An example of a secure password file.                                      //
//                                                                            //
// A straight forward implementation of a password file. This implementation  //
// can be proven to be secure. It froms the basis for the other implementation//
// variants.                                                                  //

package passwordfile;

class SecurePasswordFile {

    /*@ public final model \locset footprint; 
      @ represents footprint =
      @     \locset(names, passwords), names[*], passwords[*];
      @*/

    /*@ model int userIndex;
      @ represents userIndex \such_that
      @     0 <= userIndex && userIndex < names.length;
      @ accessible userIndex : \locset(names);
      @*/

    /*@ invariant   names.length == passwords.length;
      @*/

    private int[] names;
    private int[] passwords;


    public SecurePasswordFile(int[] names, int[] passwords) {
        this.names = names;
        this.passwords = passwords;
    }


    /**
     * Returns whether password is correct.
     */
//    /*@ normal_behavior
//      @     ensures     \result
//      @              == (   \exists int i;
//      @                     0 <= i && i < names.length;
//      @                     names[i] == user && passwords[i] == password
//      @                 );
//      @     accessible  footprint;
//      @     modifies    \nothing;
//      @     separates    names[userIndex];
//      @     separates    names[userIndex], passwords[userIndex];
//      @     separates    user, password, result;
//      @     declassify  (   \exists int i;
//      @                     0 <= i && i < names.length;
//      @                     names[i] == user && passwords[i] == password
//      @                 )
//      @                 \to \seq(user, password, result);
//      @*/
    public boolean check(int user, int password) {
        /*@ loop_invariant
          @     0 <= i
          @  && i <= names.length
          @  && (\forall int j; 0 <= j && j < i;
          @         !(names[j] == user && passwords[j] == password));
          @ assignable \nothing;
          @ decreases names.length - i;
          @*/
        for (int i = 0; i < names.length; i++) {
            if (names[i] == user &&
                passwords[i] == password) {
                return true;
            }
        }
        return false;
    }
}