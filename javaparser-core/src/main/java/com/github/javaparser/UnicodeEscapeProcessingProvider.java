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
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * {@link Provider} un-escaping unicode escape sequences in the input sequence.
 */
public class UnicodeEscapeProcessingProvider implements Provider {
	
	private static final char LF = '\n';

	private static final char CR = '\r';

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
	
	private final LineCounter _inputLine = new LineCounter();

	private final LineCounter _outputLine = new LineCounter();
	
	private final PositionMappingBuilder _mappingBuilder = new PositionMappingBuilder(_outputLine, _inputLine);
	
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
	
	/**
	 * The {@link LineCounter} of the input file.
	 */
	public LineCounter getInputCounter() {
		return _inputLine;
	}
	
	/**
	 * The {@link LineCounter} of the output file.
	 */
	public LineCounter getOutputCounter() {
		return _outputLine;
	}

	@Override
	public int read(char[] buffer, final int offset, int len) throws IOException {
		int pos = offset;
		int stop = offset + len;
		while (pos < stop) {
			int ch = _outputLine.process(nextOutputChar());
			if (ch < 0) {
				if (pos == offset) {
					// Nothing read yet, this is the end of the stream.
					return EOF;
				} else {
					break;
				}
			} else {
				_mappingBuilder.update();
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
					return clearBackSlashSeen(next);
				} else {
					return backSlashSeen();
				}
			}
			default: {
				// An arbitrary character.
				return clearBackSlashSeen(next);
			}
		}
	}

	private int clearBackSlashSeen(int next) {
		_backslashSeen = false;
		return next;
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
		return clearBackSlashSeen(ch);
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
	 * Processes column/line information from the input file.
	 * 
	 * @return The next character or <code>-1</code> if no more input is available.
	 */
	private int nextInputChar() throws IOException {
		int result = nextBufferedChar();
		return _inputLine.process(result);
	}

	/** 
	 * Retrieves the next un-escaped character from the buffered {@link #_input}.
	 * 
	 * @return The next character or <code>-1</code> if no more input is available.
	 */
	private int nextBufferedChar() throws IOException {
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
	
	/**
	 * The {@link PositionMapping} being built during processing the file.
	 */
	public PositionMapping getPositionMapping() {
		return _mappingBuilder.getMapping();
	}
	
	/**
	 * An algorithm mapping {@link Position} form two corresponding files.
	 */
	public static final class PositionMapping {
		
		private final List<DeltaInfo> _deltas = new ArrayList<>();
		
		/** 
		 * Creates a {@link UnicodeEscapeProcessingProvider.PositionMapping}.
		 */
		public PositionMapping() {
			super();
		}
		
		/**
		 * Whether this is the identity transformation.
		 */
		public boolean isEmpty() {
			return _deltas.isEmpty();
		}

		void add(int line, int column, int lineDelta, int columnDelta) {
			_deltas.add(new DeltaInfo(line, column, lineDelta, columnDelta));
		}
		
		/**
		 * Looks up the {@link PositionUpdate} for the given Position.
		 */
		public PositionUpdate lookup(Position position) {
			int result = Collections.binarySearch(_deltas, position);
			if (result >= 0) {
				return _deltas.get(result);
			} else {
				int insertIndex = -result - 1;
				if (insertIndex == 0) {
					// Before the first delta info, identity mapping.
					return PositionUpdate.NONE;
				} else {
					// The relevant update is the one with the position smaller
					// than the requested position.
					return _deltas.get(insertIndex - 1);
				}
			}
		}
		
		/**
		 * Algorithm updating a {@link Position} from one file to a
		 * {@link Position} in a corresponding file.
		 */
		public static interface PositionUpdate {
			
			/**
			 * The identity position mapping.
			 */
			PositionUpdate NONE = new PositionUpdate() {
				@Override
				public int transformLine(int line) {
					return line;
				}
				
				@Override
				public int transformColumn(int column) {
					return column;
				}
				
				@Override
				public Position transform(Position pos) {
					return pos;
				}
			};

			/** 
			 * Maps the given line to an original line.
			 */
			int transformLine(int line);

			/** 
			 * Maps the given column to an original column.
			 */
			int transformColumn(int column);

			/**
			 * The transformed position.
			 */
			default Position transform(Position pos) {
				int line = pos.line;
				int column = pos.column;
				int transformedLine = transformLine(line);
				int transformedColumn = transformColumn(column);
				return new Position(transformedLine, transformedColumn);
			}
			
		}
		
		private static final class DeltaInfo extends Position implements PositionUpdate {

			/**
			 * The offset to add to the {@link #line} and all following source
			 * positions up to the next {@link PositionUpdate}.
			 */
			private final int _lineDelta;
			
			/**
			 * The offset to add to the {@link #column} and all following
			 * source positions up to the next {@link PositionUpdate}.
			 */
			private final int _columnDelta;

			/** 
			 * Creates a {@link PositionUpdate}.
			 */
			public DeltaInfo(int line, int column, int lineDelta,
					int columnDelta) {
				super(line, column);
				_lineDelta = lineDelta;
				_columnDelta = columnDelta;
			}
			
			@Override
			public int transformLine(int sourceLine) {
				return sourceLine + _lineDelta;
			}
			
			@Override
			public int transformColumn(int sourceColumn) {
				return sourceColumn + _columnDelta;
			}
			
			@Override
			public String toString() {
				return "(" + line + ", " + column + ": " + _lineDelta + ", " + _columnDelta + ")";
			}

		}

		/** 
		 * Transforms the given {@link Position}.
		 */
		public Position transform(Position pos) {
			return lookup(pos).transform(pos);
		}

		/** 
		 * Transforms the given {@link Range}.
		 */
		public Range transform(Range range) {
			Position begin = transform(range.begin);
			Position end = transform(range.end);
			if (begin == range.begin && end == range.end) {
				// No change.
				return range;
			}
			return new Range(begin, end);
		}
	}
	
	private static final class PositionMappingBuilder {
		
		private LineCounter _left;
		
		private LineCounter _right;
		
		private final PositionMapping _mapping = new PositionMapping();
		
		private int _lineDelta = 0;
		private int _columnDelta = 0;
		
		/** 
		 * Creates a {@link PositionMappingBuilder}.
		 *
		 * @param left The source {@link LineCounter}.
		 * @param right The target {@link LineCounter}.
		 */
		public PositionMappingBuilder(LineCounter left, LineCounter right) {
			_left = left;
			_right = right;
			update();
		}
		
		/**
		 * The built {@link PositionMapping}.
		 */
		public PositionMapping getMapping() {
			return _mapping;
		}
		
		public void update() {
			int lineDelta = _right.getLine() - _left.getLine();
			int columnDelta = _right.getColumn() - _left.getColumn();
			
			if (lineDelta != _lineDelta || columnDelta != _columnDelta) {
				_mapping.add(_left.getLine(), _left.getColumn(), lineDelta, columnDelta);
				
				_lineDelta = lineDelta;
				_columnDelta = columnDelta;
			}
		}
		
	}
	
	/**
	 * Processor keeping track of the current line and column in a stream of
	 * incoming characters.
	 * 
	 * @see #process(int)
	 */
	public static final class LineCounter {
		
		/**
		 * Whether {@link #CR} has been seen on the input as last character.
		 */
		private boolean _crSeen;

		private int _line = 1;

		private int _column = 1;

		/** 
		 * Creates a {@link UnicodeEscapeProcessingProvider.LineCounter}.
		 */
		public LineCounter() {
			super();
		}
		
		/**
		 * The line of the currently processed input character.
		 */
		public int getLine() {
			return _line;
		}
		
		/**
		 * The column of the currently processed input character.
		 */
		public int getColumn() {
			return _column;
		}
		
		/** 
		 * The current position.
		 */
		public Position getPosition() {
			return new Position(getLine(), getColumn());
		}

		/** 
		 * Analyzes the given character for line feed.
		 */
		public int process(int ch) {
			switch (ch) {
				case EOF: {
					break;
				}
				case CR: {
					incLine();
					_crSeen = true;
					break;
				}
				case LF: {
					// CR LF does only count as a single line terminator.
					if (_crSeen) {
						_crSeen = false;
					} else {
						incLine();
					}
					break;
				}
				default: {
					_crSeen = false;
					_column++;
				}
			}
			return ch;
		}

		private void incLine() {
			_line++;
			_column = 1;
		}

	}
	
}
