import java.math.BigInteger;
import java.security.KeyPair;

//@ non_null_by_default
public class Test {
	
	
	public void m(KeyPair o) {
		BigInteger a = ((javax.crypto.interfaces.DHPublicKey)o.getPublic()).getY();
	}	
}

// This bug report causes a crash, but not when DHPublicKey is fully qualified 
// and the import is not used. Not sure whether this is related to the javax
// package or that DHPublicKey is an interface not yet seen. The crash relates to
// the specs for DHPublicKey not having been type-checked at a point at which they
// are referenced.
// Followup: crashes with the import, whether or not the use of DHPublicKey is fully qualified
