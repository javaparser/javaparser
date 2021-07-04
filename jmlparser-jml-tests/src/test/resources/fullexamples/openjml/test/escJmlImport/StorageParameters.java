
import org.jmlspecs.annotation.Nullable; // FIXME - should be able to get rid of this
public final class StorageParameters 
{
	public long[] configurationSizes;
	
	public StorageParameters(/*@ nullable */ long[] sizes) {  // FIXME - should be able to get rid of nullable
		this.configurationSizes = sizes;
	}
	
	long[] getConfigurationSizes() {
		return configurationSizes;
	}
	
	public static void main(String... args) {
		StorageParameters a = new StorageParameters(null);
	}
}
