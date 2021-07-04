public class ACD {

    private static long instantiate(byte[] a, byte[] b){
    	return 10;
    }

   public static class SPI  {

        private /*@ spec_public @*/ long ptr_ = 0;

       private synchronized void lazyInit() {
            if (ptr_ == 0) {
		byte[] s = new byte[64];
                ptr_ = instantiate(s, s);
		//@ assert ptr_ != 0;
            }
        }

    }
}
