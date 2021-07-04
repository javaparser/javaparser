package io;

import icecaptools.IcecapCompileMe;

import java.io.IOException;

import test.CR16C.DeviceRegByte;
import util.CircularBuffer;
import vm.InterruptDispatcher;
import vm.InterruptHandler;
import devices.CR16C.KT4585.CR16CInterruptDispatcher;
import devices.CR16C.KT4585.DeviceRegShort;

public class UARTWriter implements InterruptHandler {

	private static final short UART_TI_INT_PRIO = 0x0070;
	private static final short MAX_BUFFER = 32;

	private CircularBuffer cbuf;

	DeviceRegShort uart_clear_tx_int_reg;
	DeviceRegShort uart_ctrl_reg;
	DeviceRegShort int2_priority_reg;
	DeviceRegByte uart_rx_tx_reg;

	public UARTWriter() {
		cbuf = new CircularBuffer(MAX_BUFFER);

		uart_clear_tx_int_reg = new DeviceRegShort(0xFF4904);
		uart_ctrl_reg = new DeviceRegShort(0xFF4900);
		uart_rx_tx_reg = new DeviceRegByte(0xFF4902);
		int2_priority_reg = new DeviceRegShort(0xFF5408);
		int2_priority_reg.reg |= UART_TI_INT_PRIO;

		uart_ctrl_reg.reg |= 0xC;

		

	}

	public short capacity() {
		return MAX_BUFFER;
	}

	@Override
	@IcecapCompileMe
	public void handle() {
		if (!cbuf.isEmpty()) {
			try {
				uart_rx_tx_reg.reg = cbuf.read();
			} catch (IOException e) {
				uart_rx_tx_reg.reg = 0;
			}
			uart_ctrl_reg.reg |= 0x2;
		}
		uart_clear_tx_int_reg.reg = 0;
	}

	public void write(String str) throws IOException {
		if (str != null) {
			int length = str.length();
			for (byte i = 0; i < length; i++) {
				cbuf.write(str.charAt(i));
			}
			handle();
		} else {
			throw new IllegalArgumentException("str is null");
		}
	}

	public void write(byte b) {
		try {
			if (cbuf.isFull()) {
				flush();
				while (cbuf.isFull()) {
					;
				}
			}
			cbuf.write(b);
		} catch (IOException e) {

		}
	}

	public void flush() {
		handle();
	}

	public void writeLong(long number) {
		writeInt((int) (number >> 32));
		writeInt((int) (number & 0xFFFFFFFF));

	}

	public void writeInt(int number) {
		writeShort((short) (number >> 16));
		writeShort((short) (number & 0xFFFF));
	}

	public void writeShort(short number) {
		writeByte((byte) (number >> 8));
		writeByte((byte) (number & 0xff));
	}

	public void writeByte(byte number) {
		writeNibble((byte) ((number & 0xf0) >> 4 ));
		writeNibble((byte) (number & 0xf));
	}

	private void writeNibble(byte number) {
		if (number < 10) {
			write((byte) ('0' + number));
		} else {
			write((byte) ('A' + (number - 10)));
		}
	}

	@Override
	public void register() {
		CR16CInterruptDispatcher.init();
		InterruptDispatcher.registerHandler(this, (byte) 21);
	}

	@Override
	public void enable() {
	}

	@Override
	public void disable() {
	}
}
