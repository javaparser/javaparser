
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.ByteChannel;

public interface SB {
    
    int size();
    
    int capacity();
    
    int remaining();
    
}
