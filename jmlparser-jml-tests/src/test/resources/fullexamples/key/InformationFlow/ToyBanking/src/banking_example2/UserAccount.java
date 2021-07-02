package banking_example2;

import banking_example.*;


/**
 *
 * @author christoph
 */
public class UserAccount {
    private /*@ spec_public */ int userID;
    private /*@ spec_public */ char[] password;
    private /*@ spec_public */ int incorrectLogins;
    private BankAccount[] bankAccounts;

    /*@ public ghost \seq employeeViewOnUserAccount;
      @ public invariant employeeViewOnUserAccount ==
      @     \seq( this, userID, incorrectLogins, bankAccounts,
      @           (\seq_def int i; 0; bankAccounts.length; bankAccounts[i].customerViewOnBankAccount) );
      @
      @ public ghost \seq bankCustomerView;
      @ public invariant bankCustomerView ==
      @     \seq( this, userID, incorrectLogins, bankAccounts, password,
      @           (\seq_def int i; 0; password.length; password[i]),
      @           (\seq_def int i; 0; bankAccounts.length; bankAccounts[i].customerViewOnBankAccount) );
      @
      @ accessible \inv : this.*, password[*], bankAccounts[*];
      @
      @ public invariant 0 <= incorrectLogins && incorrectLogins <= 3;
      @*/

    /*@ normal_behavior
      @ ensures \result == (    0 <= \old(incorrectLogins)
      @                      && \old(incorrectLogins) < 3
      @                      && userID == this.userID
      @                      && password.length == this.password.length
      @                      && (\forall int i; 0 <= i && i < password.length;
      @                             password[i] == this.password[i]) );
      @ determines  incorrectLogins  \by  \itself
      @             \declassifies
      @                    (    0 <= incorrectLogins
      @                      && incorrectLogins < 3
      @                      && userID == this.userID
      @                      && password.length == this.password.length
      @                      && (\forall int i; 0 <= i && i < password.length;
      @                             password[i] == this.password[i]) )
      @             \declassifies
      @                    (    0 <= incorrectLogins
      @                      && incorrectLogins < 3
      @                      && userID == this.userID
      @                      && ( password.length != this.password.length
      @                           || (\exists int i; 0 <= i && i < password.length;
      @                                  password[i] != this.password[i]) ) );
      @ assignable  incorrectLogins, bankCustomerView, employeeViewOnUserAccount;
      @*/
    public boolean tryLogin(int userID, char[] password) {
        boolean userIDCorrect = (this.userID == userID);
        boolean pwdCorrect = (this.password.length == password.length);
        /*@ loop_invariant 0 <= i && i <= password.length;
          @ loop_invariant pwdCorrect ==
          @     (    password.length == this.password.length
          @       && (\forall int j; 0 <= j && j < i;
          @             password[j] == this.password[j]) );
          @ assignable \strictly_nothing;
          @ decreases password.length - i;
          @*/
        for(int i = 0; i < password.length && pwdCorrect; i++) {
            pwdCorrect = (this.password[i] == password[i]);
        }
        boolean incorrectLoginsInRange =
                (0 <= incorrectLogins && incorrectLogins < 3);
        
        if(userIDCorrect && incorrectLoginsInRange) {
            this.incorrectLogins = pwdCorrect ? 0 : this.incorrectLogins + 1;
        }
        /*@ set bankCustomerView =
            \seq_concat(\seq_singleton(this),
            \seq_concat(\seq_singleton(this.userID),
            \seq_concat(\seq_singleton(this.incorrectLogins),
            \seq_concat(\seq_singleton(this.bankAccounts),
            \seq_concat(\seq_singleton(this.password),
            \seq_concat(\seq_singleton(
                            // the following work-a-round is equivalent to
                            // (\seq_def int i; 0; password.length; password[i])
                            \dl_seq_def_workaround(0, this.password.length, this.password)
                                       ),
                        \seq_singleton(
                            // the following work-a-round is equivalent to
                            // (\seq_def int i; 0; bankAccounts.length; bankAccounts[i].customerViewOnBankAccount)
                            \dl_seq_def_workaround2(0, this.bankAccounts.length, this.bankAccounts, \singleton(this.bankAccounts[0].customerViewOnBankAccount))
                                      )
                        ))))));
        */
        /*@ set employeeViewOnUserAccount =
            \seq_concat(\seq_singleton(this),
            \seq_concat(\seq_singleton(this.userID),
            \seq_concat(\seq_singleton(this.incorrectLogins),
            \seq_concat(\seq_singleton(this.bankAccounts),
                        \seq_singleton(
                            // the following work-a-round is equivalent to
                            // (\seq_def int i; 0; bankAccounts.length; bankAccounts[i].customerViewOnBankAccount)
                            \dl_seq_def_workaround2(0, this.bankAccounts.length, this.bankAccounts, \singleton(this.bankAccounts[0].customerViewOnBankAccount))
                                      )
                        ))));
        */
        return userIDCorrect && pwdCorrect && incorrectLoginsInRange;
    }

    /*@ normal_behavior
      @ determines  employeeViewOnUserAccount \by \itself;
      @ determines  bankCustomerView \by  \itself;
      @ assignable \strictly_nothing;
      @*/
    public /*@ nullable */ BankAccount getBankAccount(int number) {
        if (number < 0 || bankAccounts.length <= number) {
            return null;
        }
        return bankAccounts[number];
    }
}
