package banking_example2;

import banking_example.*;


/**
 *
 * @author christoph
 */
public class BankAccount {
    private int balance;
    private int id;

    /*@ public ghost \seq customerViewOnBankAccount;
      @ public invariant customerViewOnBankAccount == \seq(this, balance, id);
      @*/

    /*@ normal_behavior
      @ determines customerViewOnBankAccount \by  \itself;
      @ assignable \strictly_nothing;
      @*/
    public int getId() {
        return id;
    }

    /*@ normal_behavior
      @ determines customerViewOnBankAccount \by  \itself;
      @ assignable \strictly_nothing;
      @*/
    public int getBalance() {
        return balance;
    }

    /*@ normal_behavior
      @ determines customerViewOnBankAccount \by  \itself
      @            \declassifies amount;
      @ assignable balance, customerViewOnBankAccount;
      @*/
    public void depositMoney(int amount) {
        this.balance = this.balance - amount;
        /*@ set customerViewOnBankAccount =
                    \seq_concat(\seq_singleton(this),
                    \seq_concat(\seq_singleton(balance),
                                \seq_singleton(id)));
        */;
    }
}
