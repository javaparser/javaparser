package devices.CR16C.KT4585;

import devices.Writer;

public class CR16ConsoleWriter implements Writer
{
	private static class UARTL2ConsoleChannel extends UARTL2Channel
	{
		public void write(byte[] bytes, short length) {
			length++;
			if (prologue(length)) {
				int bufferIndex = 0;
				write(MESSAGE);
				length--;
				while (bufferIndex < length) {
					write(bytes[bufferIndex]);
					bufferIndex++;
				}
				epilogue();
				writer.flush();
			}	
		}
	}
	
	private UARTL2ConsoleChannel channel;
	
	public CR16ConsoleWriter()
	{
		 channel = new UARTL2ConsoleChannel();
	}
	
	@Override
	public void write(byte[] bytes, short length) {
		channel.write(bytes, length);
	}
}