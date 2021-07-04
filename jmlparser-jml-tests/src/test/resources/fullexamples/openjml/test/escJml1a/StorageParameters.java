import org.jmlspecs.annotation.*;
public final class StorageParameters 
{

	private long[] configurationSizes;
	
	public StorageParameters( long[] sizes) {
		this.configurationSizes = sizes;
	}
	

	//@ ensures \fresh(\result);
	long[] getConfigurationSizes() {
		return configurationSizes;
	}
	
	public static void main(String... args) {
		StorageParameters a = new StorageParameters(null);
		@Nullable long[] b = a.getConfigurationSizes();
		//@ assert b == a.getConfigurationSizes(); // Error - fails because result is fresh
		long[] c = a.getConfigurationSizes();  // Error - c is non_null by default
	}
}
