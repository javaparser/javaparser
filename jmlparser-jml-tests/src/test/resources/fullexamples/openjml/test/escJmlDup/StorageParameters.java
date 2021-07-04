
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
		new StorageParameters(null);
	}
}
