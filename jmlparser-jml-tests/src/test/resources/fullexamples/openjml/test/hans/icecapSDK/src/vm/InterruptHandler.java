package vm;

public interface InterruptHandler 
{
    public void handle();
    
    public void register();
    
    public void enable();
    
    public void disable();
}
