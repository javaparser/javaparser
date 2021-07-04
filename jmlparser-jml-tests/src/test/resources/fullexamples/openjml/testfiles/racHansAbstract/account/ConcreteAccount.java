package account;

public class ConcreteAccount extends AbstractAccount {
	 
	public ConcreteAccount(int amt) {
	    bal = amt;
	}
	
	public void withdraw(int amt) {
	  bal -= amt;
	}
}
