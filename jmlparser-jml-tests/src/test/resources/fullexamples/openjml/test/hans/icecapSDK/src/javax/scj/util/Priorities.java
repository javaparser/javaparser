/**************************************************************************
 * File name  : Priorities.java
 * 
 * This file is part a SCJ Level 0 and Level 1 implementation, 
 * based on SCJ Draft, Version 0.94 25 June 2013.
 *
 * It is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as  
 * published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 * This SCJ Level 0 and Level 1 implementation is distributed in the hope 
 * that it will be useful, but WITHOUT ANY WARRANTY; without even the  
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this SCJ Level 0 and Level 1 implementation.  
 * If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright 2012 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *************************************************************************/

package javax.scj.util;

/**
 * Utility class with priorities.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */

public final class Priorities {
	private Priorities() {
	}

	public static final int MAX_PRIORITY = 100;
	public static final int MIN_PRIORITY = 1;
	public static final int NORM_PRIORITY = 50;

	public static final int MAX_HARDWARE_PRIORITY = 150;
	public static final int MIN_HARDWARE_PRIORITY = 101;

	public static final int PR100 = MAX_PRIORITY;

	public static final int PR99 = PR100 - 1;
	public static final int PR98 = PR100 - 2;
	public static final int PR97 = PR100 - 3;
	public static final int PR96 = PR100 - 4;
	public static final int PR95 = PR100 - 5;
	public static final int PR94 = PR100 - 6;
	public static final int PR93 = PR100 - 7;
	public static final int PR92 = PR100 - 8;
	public static final int PR91 = PR100 - 9;
	public static final int PR90 = PR100 - 10;

	public static final int SEQUENCER_PRIORITY = MIN_PRIORITY + 1; // must be lower than the handler priorities
}
