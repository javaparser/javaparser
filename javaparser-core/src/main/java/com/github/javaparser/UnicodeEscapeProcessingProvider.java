package com.github.javaparser;

import java.io.IOException;

/**
 * An implementation of interface CharStream, where the stream is assumed to
 * contain only ASCII characters (with java-like unicode escape processing).
 */
public class UnicodeEscapeProcessingProvider implements Provider {
    private static int hexval(char c) throws java.io.IOException {
        switch (c) {
            case '0':
                return 0;
            case '1':
                return 1;
            case '2':
                return 2;
            case '3':
                return 3;
            case '4':
                return 4;
            case '5':
                return 5;
            case '6':
                return 6;
            case '7':
                return 7;
            case '8':
                return 8;
            case '9':
                return 9;

            case 'a':
            case 'A':
                return 10;
            case 'b':
            case 'B':
                return 11;
            case 'c':
            case 'C':
                return 12;
            case 'd':
            case 'D':
                return 13;
            case 'e':
            case 'E':
                return 14;
            case 'f':
            case 'F':
                return 15;
        }

        throw new java.io.IOException(); // Should never come here
    }

    /**
     * Position in buffer.
     */
    private int bufpos = -1;
    private int bufsize;
    private int available;
    private int tokenBegin;
    private int bufline[];
    private int bufcolumn[];

    protected int column;
    protected int line;

    private boolean prevCharIsCR = false;
    private boolean prevCharIsLF = false;

    private Provider provider;

    private char[] nextCharBuf;
    protected char[] buffer;
    private int maxNextCharInd = 0;
    private int nextCharInd = -1;
    private int inBuf = 0;

    private void expandBuffer(boolean wrapAround) {
        char[] newbuffer = new char[bufsize + 2048];
        int newbufline[] = new int[bufsize + 2048];
        int newbufcolumn[] = new int[bufsize + 2048];

        try {
            if (wrapAround) {
                System.arraycopy(buffer, tokenBegin, newbuffer, 0, bufsize - tokenBegin);
                System.arraycopy(buffer, 0, newbuffer, bufsize - tokenBegin, bufpos);
                buffer = newbuffer;

                System.arraycopy(bufline, tokenBegin, newbufline, 0, bufsize - tokenBegin);
                System.arraycopy(bufline, 0, newbufline, bufsize - tokenBegin, bufpos);
                bufline = newbufline;

                System.arraycopy(bufcolumn, tokenBegin, newbufcolumn, 0, bufsize - tokenBegin);
                System.arraycopy(bufcolumn, 0, newbufcolumn, bufsize - tokenBegin, bufpos);
                bufcolumn = newbufcolumn;

                bufpos += (bufsize - tokenBegin);
            } else {
                System.arraycopy(buffer, tokenBegin, newbuffer, 0, bufsize - tokenBegin);
                buffer = newbuffer;

                System.arraycopy(bufline, tokenBegin, newbufline, 0, bufsize - tokenBegin);
                bufline = newbufline;

                System.arraycopy(bufcolumn, tokenBegin, newbufcolumn, 0, bufsize - tokenBegin);
                bufcolumn = newbufcolumn;

                bufpos -= tokenBegin;
            }
        } catch (Exception t) {
            throw new RuntimeException(t.getMessage());
        }

        available = (bufsize += 2048);
        tokenBegin = 0;
    }

    private void fillBuffer() throws java.io.IOException {
        int i;
        if (maxNextCharInd == 4096)
            maxNextCharInd = nextCharInd = 0;

        try {
            if ((i = provider.read(nextCharBuf, maxNextCharInd, 4096 - maxNextCharInd)) == -1) {
                provider.close();
                throw new java.io.IOException();
            } else
                maxNextCharInd += i;
        } catch (java.io.IOException e) {
            if (bufpos != 0) {
                --bufpos;
                backup(0);
            } else {
                bufline[bufpos] = line;
                bufcolumn[bufpos] = column;
            }
            throw e;
        }
    }

    private char readByte() throws java.io.IOException {
        if (++nextCharInd >= maxNextCharInd)
            fillBuffer();

        return nextCharBuf[nextCharInd];
    }

    private void adjustBufferSize() {
        if (available == bufsize) {
            if (tokenBegin > 2048) {
                bufpos = 0;
                available = tokenBegin;
            } else
                expandBuffer(false);
        } else if (available > tokenBegin)
            available = bufsize;
        else if ((tokenBegin - available) < 2048)
            expandBuffer(true);
        else
            available = tokenBegin;
    }

    private void updateLineColumn(char c) {
        column++;

        if (prevCharIsLF) {
            prevCharIsLF = false;
            line += (column = 1);
        } else if (prevCharIsCR) {
            prevCharIsCR = false;
            if (c == '\n') {
                prevCharIsLF = true;
            } else
                line += (column = 1);
        }

        int tabSize = 1;
        switch (c) {
            case '\r':
                prevCharIsCR = true;
                break;
            case '\n':
                prevCharIsLF = true;
                break;
            case '\t':
                column--;
                column += (tabSize - (column % tabSize));
                break;
            default:
                break;
        }

        bufline[bufpos] = line;
        bufcolumn[bufpos] = column;
    }

    /**
     * Read a character.
     */
    private char readChar() throws java.io.IOException {
        if (inBuf > 0) {
            --inBuf;

            if (++bufpos == bufsize)
                bufpos = 0;

            return buffer[bufpos];
        }

        char c;

        if (++bufpos == available)
            adjustBufferSize();

        if ((buffer[bufpos] = c = readByte()) == '\\') {
            updateLineColumn(c);

            int backSlashCnt = 1;

            for (; ; ) // Read all the backslashes
            {
                if (++bufpos == available)
                    adjustBufferSize();

                try {
                    if ((buffer[bufpos] = c = readByte()) != '\\') {
                        updateLineColumn(c);
                        // found a non-backslash char.
                        if ((c == 'u') && ((backSlashCnt & 1) == 1)) {
                            if (--bufpos < 0)
                                bufpos = bufsize - 1;

                            break;
                        }

                        backup(backSlashCnt);
                        return '\\';
                    }
                } catch (java.io.IOException e) {
                    // We are returning one backslash so we should only backup (count-1)
                    if (backSlashCnt > 1)
                        backup(backSlashCnt - 1);

                    return '\\';
                }

                updateLineColumn(c);
                backSlashCnt++;
            }

            // Here, we have seen an odd number of backslash's followed by a 'u'
            try {
                while ((c = readByte()) == 'u')
                    ++column;

                buffer[bufpos] = c = (char) (hexval(c) << 12 |
                        hexval(readByte()) << 8 |
                        hexval(readByte()) << 4 |
                        hexval(readByte()));

                column += 4;
            } catch (java.io.IOException e) {
                throw new RuntimeException("Invalid escape character at line " + line +
                        " column " + column + ".");
            }

            if (backSlashCnt == 1)
                return c;
            else {
                backup(backSlashCnt - 1);
                return '\\';
            }
        } else {
            updateLineColumn(c);
            return c;
        }
    }

    /**
     * Retreat.
     */
    private void backup(int amount) {

        inBuf += amount;
        if ((bufpos -= amount) < 0)
            bufpos += bufsize;
    }

    /**
     * Constructor.
     */
    private UnicodeEscapeProcessingProvider(Provider provider, int startline, int startcolumn, int buffersize) {
        this.provider = provider;
        line = startline;
        column = startcolumn - 1;

        available = bufsize = buffersize;
        buffer = new char[buffersize];
        bufline = new int[buffersize];
        bufcolumn = new int[buffersize];
        nextCharBuf = new char[4096];
    }

    /**
     * Constructor.
     */
    UnicodeEscapeProcessingProvider(Provider dstream) {
        this(dstream, 1, 1, 4096);
    }

    @Override
    public int read(char[] buffer, int offset, int len) {
        int written = 0;
        try {
            for (int i = offset; i < offset + len; i++) {
                buffer[i] = readChar();
                written++;
            }
        } catch (IOException e) {
            if (written == 0) {
                return -1;
            }
        }
        return written;
    }

    @Override
    public void close() throws IOException {
        provider.close();
    }
}
/* JavaCC - OriginalChecksum=5b3a48657b00e1766eaec2b5683a555c (do not edit this line) */
