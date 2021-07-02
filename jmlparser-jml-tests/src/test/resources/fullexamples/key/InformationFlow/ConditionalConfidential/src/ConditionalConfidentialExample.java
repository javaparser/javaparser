/**
 * ConditionalConfidentialExample
 * @author christoph
 */
public class ConditionalConfidentialExample {
    private User[] trustworthyUsers;
    private int confidentialData;

    /*@ normal_behavior
      @ determines u, u.data,
      @            hasAccessRight(u),
      @            (hasAccessRight(u) ? confidentialData : 0)
      @        \by \itself;
      @*/
    public void getConfidentialData(User u) {
        if (hasAccessRight(u)) {
            u.setData(confidentialData);
        }
    }

    /*@ normal_behavior
      @ ensures \result ==
      @         (\exists int i; 0 <= i && i < trustworthyUsers.length;
      @                                             trustworthyUsers[i] == u);
      @*/
    private /*@ pure */ boolean hasAccessRight(User u) {
        /*@ loop_invariant 0 <= i && i <= trustworthyUsers.length;
          @ loop_invariant
          @     (\forall int j; 0 <= j && j < i; trustworthyUsers[j] != u);
          @ assignable \nothing;
          @ decreases trustworthyUsers.length - i;
          @*/
        for (int i = 0; i < trustworthyUsers.length; i++) {
            if (trustworthyUsers[i] == u) {
                return true;
            }
        }
        return false;
    }

    public class User {
        private /*@ spec_public */ int data;

        // implemented as final to make method inling sound
        final void setData(int data) {
            this.data = data;
        }
    }
}
