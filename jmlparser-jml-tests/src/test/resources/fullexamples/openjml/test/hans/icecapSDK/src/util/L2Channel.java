package util;

public class L2Channel {
	private static final int L2_PACKET_SIZE = 128;

	private static final int L2_BUFFER_SIZE = (L2_PACKET_SIZE * 2 + 4);

	private static final int DLE = 0x10;

	private static final int STX = 0x02;

	private static final int ETX = 0x03;

	private enum L2Error {
		DLE_ERROR, // DLE is followed by a value different from STX,ETX or DLE
		L2_RX_OVERFLOW, // L2 RX buffer Overflow
		L2_TX_OVERFLOW, // L2 TX Buffer is overflow
		CHSUM_ERROR, // Error in the caculated/received packet checksum
		LENGTH_FIELD_ERROR, // Length field in packet to long/short
		MISSING_START, // The first characters must be a DLE STX sequence
		LAST_L2_ERROR
		// Must always be the last number in enum!!
	};

	private static String getL2ErrorString(L2Error error) {
		String result = null;

		switch (error) {
		case DLE_ERROR:
			result = "DLE_ERROR";
			break;
		case L2_RX_OVERFLOW:
			result = "L2_RX_OVERFLOW";
			break;
		case L2_TX_OVERFLOW:
			result = "L2_TX_OVERFLOW";
			break;
		case CHSUM_ERROR:
			result = "CHSUM_ERROR";
			break;
		case LENGTH_FIELD_ERROR:
			result = "LENGTH_FIELD_ERROR";
			break;
		case MISSING_START:
			result = "MISSING_START";
			break;
		case LAST_L2_ERROR:
			result = "LAST_L2_ERROR";
			break;
		default:
			result = "UNKNONW";
		}
		return result;
	}

	private enum l2_state_t {
		L2_SYNC_STATE, L2_WAIT_STX_STATE, L2_RECV_STATE, L2_DLE_STATE
	};

	private class L2ControlType {
		@SuppressWarnings("unused")
		public long RXSignal_cnt; // Total number of signals received on L2

		@SuppressWarnings("unused")
		public long RXData_cnt; // Total number of data bytes received on L2

		// (excl. DLE, STX, ETX & Bytestuffing)

		@SuppressWarnings("unused")
		public long RXBuffer_cnt; // Total number of bytes received on L2

		@SuppressWarnings("unused")
		public long TXSignal_cnt; // Total number of signals sent on L2

		@SuppressWarnings("unused")
		public long TXData_cnt; // Total number of data bytes sent on L2

		// (excl. DLE, STX, ETX & Bytestuffing)

		@SuppressWarnings("unused")
		public long TXBuffer_cnt; // Total number of bytes sent on L2

		public L2ControlType() {
			RXSignal_cnt = RXData_cnt = RXBuffer_cnt = TXSignal_cnt = TXData_cnt = TXBuffer_cnt = 0;
		}
	}

	private L2ControlType L2Control;

	private l2_state_t l2_state;;

	private byte[] l2_recv_buffer;

	private byte[] l2_send_buffer;

	private int l2_recv_buffer_ptr;

	private short ptr;
	private byte checksum;

	private IL2ErrorHandler errorHandler;

	public L2Channel(IL2ErrorHandler errorHandler) {
		this.errorHandler = errorHandler;

		L2Control = new L2ControlType();
		l2_state = l2_state_t.L2_SYNC_STATE;
		l2_recv_buffer_ptr = 0;

		l2_recv_buffer = new byte[L2_BUFFER_SIZE];
		l2_send_buffer = new byte[L2_BUFFER_SIZE];
	}

	public void receive_callback(byte[] msg) {
		;
	}

	public void send_callback(byte[] msg, short ptr) {
		;
	}

	private void L2ErrorHandler(L2Error error, byte offendingByte) {
		if (errorHandler != null) {
			errorHandler.errorOccurred(getL2ErrorString(error), offendingByte);
		}
	}

	private static short l2_stuff(byte[] buffer, short ptr, byte c) {
		if (c == DLE) {
			buffer[ptr++] = DLE;
		}
		buffer[ptr++] = c;
		return ptr;
	}

	synchronized public final void l2_send(byte[] buffer) {
		if (prologue((short) buffer.length)) {
			int bufferIndex = 0;

			while (bufferIndex < buffer.length) {
				write(buffer[bufferIndex]);
				bufferIndex++;
			}

			epilogue();
		}
	}

	protected void epilogue() {
		ptr = l2_stuff(l2_send_buffer, ptr, checksum);

		l2_send_buffer[ptr++] = DLE;
		l2_send_buffer[ptr++] = ETX;

		L2Control.TXBuffer_cnt += ptr;

		send_callback(l2_send_buffer, (short) ptr);
	}

	protected void write(byte b) {
		ptr = l2_stuff(l2_send_buffer, ptr, b);
		checksum += b;
	}

	public boolean prologue(short length) {
		ptr = 0;
		checksum = 0;

		L2Control.TXSignal_cnt++;
		L2Control.TXData_cnt += length;

		if (length >= L2_PACKET_SIZE) {
			L2ErrorHandler(L2Error.L2_TX_OVERFLOW, (byte) 0);
			return false;
		}

		l2_send_buffer[ptr++] = DLE;
		l2_send_buffer[ptr++] = STX;

		ptr = l2_stuff(l2_send_buffer, ptr, (byte) (length & 0xff));
		ptr = l2_stuff(l2_send_buffer, ptr, (byte) ((length >> 8) & 0xff));
		return true;
	}

	synchronized public final void l2_recv(byte[] buffer) {
		int length = buffer.length;
		L2Control.RXBuffer_cnt += length; // Total number of signals
		int index = 0;
		// received on L2
		while (length-- > 0) {
			switch (l2_state) {
			case L2_SYNC_STATE:
				if (buffer[index] == DLE)
					l2_state = l2_state_t.L2_WAIT_STX_STATE;
				else
					L2ErrorHandler(L2Error.MISSING_START, buffer[index]);
				break;

			case L2_WAIT_STX_STATE:
				if (buffer[index] == STX) {
					l2_state = l2_state_t.L2_RECV_STATE;
					l2_recv_buffer_ptr = 0;
				} else if (buffer[index] != DLE) {
					l2_state = l2_state_t.L2_SYNC_STATE;
					L2ErrorHandler(L2Error.MISSING_START, buffer[index]);
				}
				break;

			case L2_RECV_STATE:
				if (buffer[index] == DLE)
					l2_state = l2_state_t.L2_DLE_STATE;
				else {
					l2_recv_buffer[l2_recv_buffer_ptr++] = buffer[index];
				}
				break;

			case L2_DLE_STATE:
				if (buffer[index] == DLE) {
					l2_recv_buffer[l2_recv_buffer_ptr++] = DLE;
					l2_state = l2_state_t.L2_RECV_STATE;
				} else if (buffer[index] == ETX) {
					short message_length = (short) (l2_recv_buffer[0] | (l2_recv_buffer[1] << 8));
					byte checksum;
					int i;
					if (message_length != l2_recv_buffer_ptr - 3) {
						L2ErrorHandler(L2Error.LENGTH_FIELD_ERROR, (byte) 0);
						l2_state = l2_state_t.L2_SYNC_STATE;
						continue;
					}

					// Normal Checksum compensates for an error in the BMC
					// code, this error is not in the Simulated BMC
					for (i = 0, checksum = 0; i < message_length; i++)
						checksum += l2_recv_buffer[2 + i];

					if (checksum != l2_recv_buffer[2 + message_length]) {
						l2_state = l2_state_t.L2_SYNC_STATE;
						L2ErrorHandler(L2Error.CHSUM_ERROR, (byte) 0);
						continue;
					}

					L2Control.RXSignal_cnt++;
					L2Control.RXData_cnt += message_length;
					{
						byte[] message = new byte[message_length];
						for (int count = 0; count < message_length; count++) {
							message[count] = l2_recv_buffer[count + 2];
						}
						receive_callback(message);
					}
					l2_state = l2_state_t.L2_SYNC_STATE;
				} else {
					l2_state = l2_state_t.L2_SYNC_STATE;
					L2ErrorHandler(L2Error.DLE_ERROR, (byte) 0);
				}
				break;
			}
			index++;
			if (l2_recv_buffer_ptr >= L2_BUFFER_SIZE) {
				l2_state = l2_state_t.L2_SYNC_STATE;
				L2ErrorHandler(L2Error.L2_RX_OVERFLOW, (byte) 0);
			}
		}
	}
}
