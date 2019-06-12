/*
 * Copyright (C) 2019 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser;

import java.io.IOException;

/**
 * {@link Provider} un-escaping unicode escape sequences in the input sequence.
 */
public class UnicodeEscapeProcessingProvider implements Provider {
	
	private static final char BACKSLASH = '\\';

	private static final int EOF = -1;
	
	private char[] _data;
	
	/**
	 * The number of characters in {@link #_data}.
	 */
	private int _len = 0;
	
	/**
	 * The position in {@link #_data} where to read the next source character from.
	 */
	private int _pos = 0;

	private boolean _backslashSeen;

	private Provider _input;

	/** 
	 * Creates a {@link UnicodeEscapeProcessingProvider}.
	 */
	public UnicodeEscapeProcessingProvider(Provider input) {
		this(2048, input);
	}

	/** 
	 * Creates a {@link UnicodeEscapeProcessingProvider}.
	 */
	public UnicodeEscapeProcessingProvider(int bufferSize, Provider input) {
		_input = input;
		_data = new char[bufferSize];
	}

	@Override
	public int read(char[] buffer, final int offset, int len) throws IOException {
		int pos = offset;
		int stop = offset + len;
		while (pos < stop) {
			int ch = nextOutputChar();
			if (ch < 0) {
				if (pos == offset) {
					// Nothing read yet, this is the end of the stream.
					return EOF;
				} else {
					break;
				}
			} else {
				buffer[pos++] = (char) ch;
			}
		}
		return pos - offset;
	}

	@Override
	public void close() throws IOException {
		_input.close();
	}

	/** 
	 * Produces the next un-escaped character to be written to the output.
	 * 
	 * @return The next character or <code>-1</code> if no more characters are available.
	 */
	private int nextOutputChar() throws IOException {
		int next = nextInputChar();
		switch (next) {
			case EOF:
				return EOF;
			case BACKSLASH: {
				if (_backslashSeen) {
					// This is a backslash in an odd position. It is not eligible to form an unicode escape sequence.
					_backslashSeen = false;
					return next;
				} else {
					return backSlashSeen();
				}
			}
			default: {
				// An arbitrary character.
				_backslashSeen = false;
				return next;
			}
		}
	}

	private int backSlashSeen() throws IOException {
		_backslashSeen = true;
		
		int next = nextInputChar();
		switch (next) {
			case EOF:
				// End of file after backslash produces the backslash itself.
				return BACKSLASH;
			case 'u': {
				return unicodeStartSeen();
			}
			default: {
				pushBack(next);
				return BACKSLASH;
			}
		}
	}

	private int unicodeStartSeen() throws IOException {
		int uCnt = 1;
		while (true) {
			int next = nextInputChar();
			switch (next) {
				case EOF: {
					pushBackUs(uCnt);
					return BACKSLASH;
				}
				case 'u': {
					uCnt++;
					continue;
				}
				default: {
					return readDigits(uCnt, next);
				}
			}
		}
	}

	private int readDigits(int uCnt, int next3) throws IOException {
		int digit3 = digit(next3);
		if (digit3 < 0) {
			pushBack(next3);
			pushBackUs(uCnt);
			return BACKSLASH;
		}
		
		int next2 = nextInputChar();
		int digit2 = digit(next2);
		if (digit2 < 0) {
			pushBack(next2);
			pushBack(next3);
			pushBackUs(uCnt);
			return BACKSLASH;
		}
		
		int next1 = nextInputChar();
		int digit1 = digit(next1);
		if (digit1 < 0) {
			pushBack(next1);
			pushBack(next2);
			pushBack(next3);
			pushBackUs(uCnt);
			return BACKSLASH;
		}
		
		int next0 = nextInputChar();
		int digit0 = digit(next0);
		if (digit0 < 0) {
			pushBack(next0);
			pushBack(next1);
			pushBack(next2);
			pushBack(next3);
			pushBackUs(uCnt);
			return BACKSLASH;
		}

		int ch = digit3 << 12 | digit2 << 8 | digit1 << 4 | digit0;
		_backslashSeen = false;
		return ch;
	}

	private void pushBackUs(int cnt) {
		for (int n = 0; n < cnt; n++) {
			pushBack('u');
		}
	}

	private static int digit(int ch) {
		if (ch >= '0' && ch <= '9') {
			return ch - '0';
		}
		if (ch >= 'A' && ch <= 'F') {
			return 10 + ch - 'A';
		}
		if (ch >= 'a' && ch <= 'f') {
			return 10 + ch - 'a';
		}
		return -1;
	}

	/** 
	 * Retrieves the next un-escaped character from the buffered {@link #_input}.
	 * 
	 * @return The next character to output or <code>-1</code> if no more input is available.
	 */
	private int nextInputChar() throws IOException {
		while (isBufferEmpty()) {
			int direct = fillBuffer();
			if (direct < 0) {
				return EOF;
			}
		}
		return _data[_pos++];
	}

	private boolean isBufferEmpty() {
		return _pos >= _len;
	}

	private int fillBuffer() throws IOException {
		_pos = 0;
		int direct = _input.read(_data, 0, _data.length);
		if (direct != 0) {
			_len = direct;
		}
		return direct;
	}

	private void pushBack(int ch) {
		if (ch < 0) {
			return;
		}
		
		if (isBufferEmpty()) {
			_pos = _data.length;
			_len = _data.length;
		} else if (_pos == 0) {
			if (_len == _data.length) {
				// Buffer is completely full, no push possible, enlarge buffer.
				char[] newData = new char[_data.length + 1024];
				_len = newData.length;
				_pos = newData.length - _data.length;
				System.arraycopy(_data, 0, newData, _pos, _data.length);
				_data = newData;
			} else {
				// Move contents to the right.
				int cnt = _len - _pos;
				_pos = _data.length - _len;
				_len = _data.length;
				System.arraycopy(_data, 0, _data, _pos, cnt);
			}
		}
		_data[--_pos] = (char) ch;
	}
	
}
