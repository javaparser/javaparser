
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.Random;
//import java.util.function.Function;


public class SBB implements SB {
    
    private final ByteBuffer buf;
    private int size;
    
    private SBB(ByteBuffer buf, int size) {
	this.buf = buf;
	this.size = size;
    }
    
    /**
     * Create a new buffer in direct memory with the given capacity.
     */
    public static SBB allocateDirect(int n) {
	return null;
    }
    
}
