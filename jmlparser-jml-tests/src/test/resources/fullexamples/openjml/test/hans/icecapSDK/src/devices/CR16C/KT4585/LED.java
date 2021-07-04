package devices.CR16C.KT4585;

public class LED {

    Port P2;
    
    public LED()
    {
        P2 = new Port(0xFF4850);
        P2.mode &= ~Port.P2_1_MODE;
        P2.dir |= Port.Px_1_DIR;
        off();
    }

    public void off() {
        P2.reset |= Port.Px_1_SET;
    }
    
    public void on() {
        P2.set |= Port.Px_1_SET;
    }
}
