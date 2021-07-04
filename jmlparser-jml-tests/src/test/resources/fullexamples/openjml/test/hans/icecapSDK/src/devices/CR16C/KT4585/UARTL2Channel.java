package devices.CR16C.KT4585;

import io.UARTWriter;
import util.IL2ErrorHandler;
import util.L2Channel;

public class UARTL2Channel extends L2Channel
{
	protected static final byte MESSAGE = 0x42;
	
	private static class UARTChannelErrorHandler implements IL2ErrorHandler
	{
		@Override
		public void errorOccurred(String errorString, byte offendingByte) {
			devices.Console.println(errorString);
		}
	}
	
	protected UARTWriter writer;
	
	public UARTL2Channel() {
		super(new UARTChannelErrorHandler());
		writer = new UARTWriter();
		writer.register();
	}

	@Override
	public void send_callback(byte[] msg, short length) {
		for (byte index = 0; index < length; index++)
		{
			writer.write(msg[index]);
		}
		writer.flush();
	}

	public void write(String string) {
		short length = (short) string.length();
		
		length++;
		if (prologue(length)) {
			int bufferIndex = 0;
			write(MESSAGE);
			length--;
			while (bufferIndex < length) {
				write((byte)string.charAt(bufferIndex));
				bufferIndex++;
			}
			epilogue();
		}			
	}
}

