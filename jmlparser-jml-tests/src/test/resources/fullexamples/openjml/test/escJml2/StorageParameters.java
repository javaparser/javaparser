

public final class StorageParameters 
{

	private long[] configurationSizes;
	

	public StorageParameters(long[] sizes) {

		this.configurationSizes = sizes;
	}
	
	
	long[] getConfigurationSizes() {
		return configurationSizes;
	}
	
	public static void main(String... args) {
		StorageParameters a = new StorageParameters(null);
		/*@ nullable */ long[] b = a.getConfigurationSizes();
		long[] c = a.getConfigurationSizes();  // OK - c is nullable by default
	}
}
