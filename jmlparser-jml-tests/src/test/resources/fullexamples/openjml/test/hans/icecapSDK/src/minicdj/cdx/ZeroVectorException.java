/**
 *  This file is part of miniCDx benchmark of oSCJ.
 *
 *   miniCDx is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   miniCDx is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with miniCDx.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *   Copyright 2009, 2010 
 *   @authors  Daniel Tang, Ales Plsek
 *
 *   See: http://sss.cs.purdue.edu/projects/oscj/
 */
package minicdj.cdx;

/**
 * The <code>ZeroVectorException</code> exception is thrown by utilities that perform calculations on vectors. If a
 * particular operation is undefined for the zero vector, a <code>ZeroVectorException</code> exception is thrown. The
 * motivation for this class (as opposed to using a standard <code>ArithmeticException</code>) is to allow filtering
 * based on the type of the exception.
 * 
 * @author Ben L. Titzer
 **/
class ZeroVectorException extends ArithmeticException {

    /**
	  * 
	  */
    private static final long serialVersionUID = 6064932560449189963L;

    /**
     * The only constructor for the <code>ZeroVectorException</code> class takes a string as an argument and simply
     * calls the super constructor.
     * 
     * @param msg
     *            a message describing the operation that caused the exception
     **/
    public ZeroVectorException(String msg) {
        super(msg);
    }
}
