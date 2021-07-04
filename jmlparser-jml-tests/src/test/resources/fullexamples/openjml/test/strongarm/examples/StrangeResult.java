public class StrangeResult {
    
    
    public int h(){
   
	int prime = 14747;
   	int result = prime + this.hashCode();
   	result = prime * result + this.hashCode();
   	return prime * result + this.hashCode();
   	
    }
    
    
    
    
}