/**************************************************************************
 * File name  : MyApp.java
 * 
 * This code is available under the license:
 * Creative Commons, http://creativecommons.org/licenses/by-nc-nd/3.0/
 * It is free for non-commercial use. 
 * 
 * VIA University College, Horsens, Denmark, 2011
 * Hans Soendergaard, hso@viauc.dk
 * 
 * Description: 
 * 
 * Revision history:
 *   date   init  comment
 *
 *************************************************************************/

package minicdj;

import javax.realtime.PriorityParameters;
import javax.safetycritical.Launcher;
import javax.safetycritical.Mission;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.Safelet;
import javax.safetycritical.StorageParameters;
import javax.scj.util.Const;
import javax.scj.util.Priorities;

import minicdj.cdx.Constants;
import minicdj.cdx.Level0Safelet;
import minicdj.utils.Utils;

@SuppressWarnings("rawtypes")
public class MyApp implements Safelet {
	public MissionSequencer getSequencer() {
		devices.Console.println("** MyApp.getSequencer");
		return new MySequencer();
	}

	public long immortalMemorySize() {
		return Const.IMMORTAL_MEM;
	}

	public static void main(String[] args) {
		devices.Console.println("\n****** mini cdj: main.begin");

		if (args.length > 0)
			Constants.NUMBER_OF_PLANES = Integer.parseInt(args[0]);
		if (args.length > 1)
			Constants.DETECTOR_PERIOD = Integer.parseInt(args[1]);
		if (args.length > 2)
			Constants.MAX_FRAMES = Integer.parseInt(args[2]);
		Utils.debugPrint("Planes: " + Constants.NUMBER_OF_PLANES);
		Utils.debugPrint("Period: " + Constants.DETECTOR_PERIOD);
		Utils.debugPrint("Frames: " + Constants.MAX_FRAMES);

		//  executes in heap memory
		new Launcher(new MyApp(), 0);

		devices.Console.println("   ****** mini cdj: main.end **************");
	}

	final class MySequencer extends MissionSequencer {
		private Level0Safelet mission;

		MySequencer() {
			super(
					new PriorityParameters(Priorities.PR99),
					new StorageParameters(Const.PRIVATE_MEM, null, 0, 0, 0));

			devices.Console
					.println("---- MySequencer.constructor: super finished");

			mission = new Level0Safelet(); // with information about size of mission memory 
			mission.setup();

			devices.Console
					.println("MySequencer.constructor: MyMission created");
		}

		public Mission getNextMission() {
			if (mission.terminationPending()) {
				devices.Console
						.println("\n ** MySequencer.getNextMission: null \n    missionTerminate: "
								+ mission.terminationPending());
				mission.teardown();

				return null;
			} else {
				devices.Console.println("\nMySequencer.getNextMission:"
						+ mission + "\n    missionTerminate: "
						+ mission.terminationPending());
				return mission;
			}
		}
	}

	@Override
	public void initializeApplication() {

	}
}
