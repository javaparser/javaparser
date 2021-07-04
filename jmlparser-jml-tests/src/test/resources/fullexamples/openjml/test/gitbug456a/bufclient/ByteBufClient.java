package bufclient;

import bytebuf.ByteBuf;

public class ByteBufClient {
	public /*@ pure @*/ byte getOne(ByteBuf b) {
		return b.get(0);
	}
}
