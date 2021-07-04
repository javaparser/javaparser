
public final class StorageParameters 
{
	private long totalBackingStore;
	private long[] configurationSizes;
	
	public StorageParameters(long totalBackingStore, long[] sizes) {

		this.totalBackingStore = totalBackingStore;
		this.configurationSizes = sizes;
	}
	

	//used in JML annotation only (not public)
	long getBackingStoreSize() {
		return totalBackingStore;
	}
	
	//used in JML annotation only (not public)
	long[] getConfigurationSizes() {
		return configurationSizes;
	}
	
	public static void main(String... args) {
		new StorageParameters(1L,null);
	}
}
