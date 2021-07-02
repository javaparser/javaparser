package banking_example2;

import banking_example.*;


/**
 *
 * @author christoph
 */
public class Bank {

    private UserAccount[] userAccounts;

    /*@ public model \seq bankEmployeeView;
      @ public represents bankEmployeeView =
      @     \seq( userAccounts,
      @           (\seq_def int i; 0; userAccounts.length; userAccounts[i].employeeViewOnUserAccount) );
      @
      @ public invariant ( \forall int i; 0 <= i && i < userAccounts.length; \invariant_for(userAccounts[i]) );
      @
      @ public ghost int anyID;
      @ public invariant 0 <= anyID && anyID < userAccounts.length;
      @*/

    /*@ normal_behavior
//      @ determines  \result
//      @        \by  userID,
//      @             (\seq_def int i; 0; password.length; password[i]),
//      @             (   0 <= userID && userID < userAccounts.length
//      @              && userAccounts[userID].tryLogin(userID, password))
//      @             ? userAccounts[userID] : null
//      @        \declassifies userAccounts[userID].tryLogin(userID, password);
//      @ determines  \result
//      @        \by  userID,
//      @             (\seq_def int i; 0; password.length; password[i]),
//      @             (   0 <= userID && userID < userAccounts.length
//      @                  && 0 <= userAccounts[userID].incorrectLogins
//      @                  && userAccounts[userID].incorrectLogins < 3
//      @                  && userID == userAccounts[userID].userID
//      @                  && password.length == userAccounts[userID].password.length
//      @                  && (\forall int i; 0 <= i && i < password.length;
//      @                             password[i] == userAccounts[userID].password[i]) )
//      @             ? userAccounts[userID] : null
//      @        \declassifies
//      @                   0 <= userAccounts[userID].incorrectLogins
//      @                && userAccounts[userID].incorrectLogins < 3
//      @                && userID == userAccounts[userID].userID
//      @                && password.length == userAccounts[userID].password.length
//      @                && (\forall int i; 0 <= i && i < password.length;
//      @                             password[i] == userAccounts[userID].password[i]);
      @ determines  bankEmployeeView \by \itself
      @             \declassifies userID
      @             \declassifies
      @                    (    0 <= userAccounts[userID].incorrectLogins
      @                      && userAccounts[userID].incorrectLogins < 3
      @                      && userID == userAccounts[userID].userID
      @                      && password.length == userAccounts[userID].password.length
      @                      && (\forall int i; 0 <= i && i < password.length;
      @                             password[i] == userAccounts[userID].password[i]) )
      @             \declassifies
      @                    (    0 <= userAccounts[userID].incorrectLogins
      @                      && userAccounts[userID].incorrectLogins < 3
      @                      && userID == userAccounts[userID].userID
      @                      && ( password.length != userAccounts[userID].password.length
      @                           || (\exists int i; 0 <= i && i < password.length;
      @                                  password[i] != userAccounts[userID].password[i]) ) );
//      @ // The underspecified integer anyID is used to quantify over all userAccounts:
//      @ determines  userAccounts[anyID].bankCustomerView \by \itself
//      @             \declassifies anyID == userID
//      @             \declassifies
//      @                    (    0 <= userAccounts[userID].incorrectLogins
//      @                      && userAccounts[userID].incorrectLogins < 3
//      @                      && userID == userAccounts[userID].userID
//      @                      && password.length == userAccounts[userID].password.length
//      @                      && (\forall int i; 0 <= i && i < password.length;
//      @                             password[i] == userAccounts[userID].password[i]) )
//      @             \declassifies
//      @                    (    0 <= userAccounts[userID].incorrectLogins
//      @                      && userAccounts[userID].incorrectLogins < 3
//      @                      && userID == userAccounts[userID].userID
//      @                      && ( password.length != userAccounts[userID].password.length
//      @                           || (\exists int i; 0 <= i && i < password.length;
//      @                                  password[i] != userAccounts[userID].password[i]) ) );
      @*/
    public /*@ nullable */ UserAccount login(int userID,
                                             char[] password) {
        if (0 <= userID &&
                 userID < userAccounts.length &&
                 userAccounts[userID].tryLogin(userID, password)) {
            return userAccounts[userID];
        } else {
            return null;
        }
    }

}
