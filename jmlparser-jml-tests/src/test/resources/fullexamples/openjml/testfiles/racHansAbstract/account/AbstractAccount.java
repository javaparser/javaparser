package account;

public abstract class AbstractAccount {
	
  int bal;
	
  public int balance(){
    return bal;
  }	
	
  public abstract void withdraw(int amt);
  
  //used for JML annotation only (not public)
  int getBalance() {
  	return bal;
  }

}
