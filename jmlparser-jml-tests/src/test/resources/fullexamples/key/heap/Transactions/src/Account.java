final class Account {
    /*@nullable*/ Transaction transactions;
    
    //@ ghost int balance;
    //@ ghost \locset footprint;

    /*@ invariant transactions == null || 
           (transactions.\inv && 
           \disjoint(this.*, transactions.footprint));
    */
    
    /*@ invariant balance == 
        (transactions == null ? 0 : transactions.total);
    */

    /*@ invariant footprint == \set_union(\all_fields(this),
         (transactions == null) ? \empty : transactions.footprint);
    */

    //@ invariant balance >= 0;

    //@ accessible \inv: footprint;

    /*@ requires true;
      @ ensures transactions == null && balance == 0;
      @ modifies \nothing;
      @*/
    Account() {
        /*@ set footprint = \all_fields(this); */
        transactions = null;
    }

    /*@ requires 0 <= amount;
      @ ensures balance == \old(balance) + amount;
      @ modifies this.*;
      @*/
    void deposit(int amount) {
        Transaction t = new Transaction(transactions, amount);
        transactions = t;
        //@ set balance = balance + amount;
        /*@ set footprint = \set_union(\all_fields(this),
                  transactions.footprint);
        */;
    }

    /*@ requires 0 <= amount && amount <= balance;
      @ ensures balance == \old(balance) - amount;
      @ modifies this.*;
      @*/
    void withdraw(int amount) {
        Transaction t = new Transaction(transactions, -amount);
        transactions = t;
        //@ set balance = balance - amount;
        /*@ set footprint = \set_union(\all_fields(this),
                  transactions.footprint);
        */;
    }

    /*@ requires 0 <= amount && amount <= balance && 
      @     to.\inv && to != this;
      @ ensures balance == \old(balance) - amount && 
      @     to.balance == \old(to.balance) + amount && 
      @     to.\inv;
      @ modifies this.*, to.*;
      @*/
    void transfer(Account to, int amount) {
        withdraw(amount);
        to.deposit(amount);
        // while(false);
    }

    /*@ requires true;
      @ ensures \result == balance;
      @ modifies \nothing;
      @*/
    int getTotal() {
        if(transactions == null) {
            return 0;
        } else {
            return transactions.getTotal();
        }
    }
}

class Main {

    /*@ requires true;
      @ ensures true;
      @*/
    void main() {
        Account a1 = new Account();
        a1.deposit(100);

        Account a2 = new Account();

        a2.deposit(200);
        a1.transfer(a2, 50);
        
        if(a2.getTotal() != 250)
            throw new Error();

        if(a1.getTotal() != 50)
            throw new Error();
    }
}
