
import org.jmlspecs.annotation.*;
public class TCWithJml {
	
    public Object mm() { return null; }
    
    @NonNull
    public Object m2() { return null; }

    @NonNull
    public Object m2ok() { return null; }

    public Object m3() { return null; }
    public Object m3a() { return null; }

    public Object m4() { return null; }
    public Object m4a() { return null; }

	final int f;
	@NonNull Object f1;   // Warning - annotation ignored
    Object f2;
    Object f2a;
    Object f3;
    Object f3a;
    @Nullable Object fok;
	
	public static Object m(final int i, int j, int k, final int l) {
		return null;
	}
	
	public static Object p(@Nullable Integer i, Integer j, Integer k, @Nullable  Integer l) {  // Warning - annotation ignored
		return null;
	}

    public static Object q(Integer j) { return null; }

    public static Object r(Integer j) { return null; }
    public static Object qa(Integer j) { return null; }

    public static Object ra(Integer j) { return null; }
    
}

@Pure
class AA {}

final class BB {}

@Pure final class CC {}

class DD {}

class EE {}