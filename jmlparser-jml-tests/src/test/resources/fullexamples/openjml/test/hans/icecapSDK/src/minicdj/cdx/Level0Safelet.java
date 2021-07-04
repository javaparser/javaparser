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

import icecaptools.IcecapCompileMe;
import minicdj.simulator.immortal.Simulator;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;
import javax.realtime.RelativeTime;
import javax.safetycritical.Frame;
import javax.safetycritical.CyclicExecutive;
import javax.safetycritical.CyclicSchedule;
import javax.safetycritical.PeriodicEventHandler;

import minicdj.cdx.unannotated.NanoClock;

/*@javax.safetycritical.annotate.Scope("immortal")*/
public class Level0Safelet extends CyclicExecutive {
    public Level0Safelet() {
        super();
    }

    public void setup() {
        Constants.PRESIMULATE = true;
        new ImmortalEntry().run();
        new Simulator().generate();
    }

    public void teardown() {
        devices.Console.println("Level0Safelet.teardown");
        dumpResults();
    }

    public CyclicSchedule getSchedule(PeriodicEventHandler[] handlers) {
        Frame[] frames = new Frame[1];
        CyclicSchedule schedule = new CyclicSchedule(frames);
        
        // HSO hack, 29Jan2013: only one handler
        PeriodicEventHandler[] handlerArr = new PeriodicEventHandler[1];
        handlerArr[0] = handlers[0];
        frames[0] = new Frame(new RelativeTime(Constants.DETECTOR_PERIOD, 0), handlerArr);
        
        //frames[0] = new CyclicSchedule.Frame(new RelativeTime(Constants.DETECTOR_PERIOD, 0), handlers);
        //devices.Console.println("MiniCDj.Level0Safelet.getSchedule, n: " + handlerArr.length);
        return schedule;
    }

    /*@javax.safetycritical.annotate.RunsIn("cdx.Level0Safelet")*/
    @IcecapCompileMe
    protected void initialize() {
        try {
            ImmortalEntry.detectorThreadStart = NanoClock.now();
            AbsoluteTime releaseAt = NanoClock.roundUp(Clock.getRealtimeClock().getTime().add(
                Constants.DETECTOR_STARTUP_OFFSET_MILLIS, 0));
            ImmortalEntry.detectorFirstRelease = NanoClock.convert(releaseAt);
            
            new CollisionDetectorHandler(this).register();

            if (Constants.DEBUG_DETECTOR) {
                devices.Console.println("Detector thread is " + Thread.currentThread());
                devices.Console
                    .println("Entering detector loop, detector thread priority is "
                            + "Unknown" + " (NORM_PRIORITY is " + Thread.NORM_PRIORITY
                            + ", MIN_PRIORITY is " + Thread.MIN_PRIORITY + ", MAX_PRIORITY is " + Thread.MAX_PRIORITY
                            + ")");
            }

        } catch (Throwable e) {
            devices.Console.println("e: " + e.getMessage());
            e.printStackTrace();
        }
    }

    public long missionMemorySize() {
        return Constants.PERSISTENT_DETECTOR_SCOPE_SIZE;
    }

    public static void dumpResults() {
        
        String space = " ";
        String triZero = " 0 0 0 ";

        if (Constants.PRINT_RESULTS) {
            devices.Console
                .println("Dumping output [ timeBefore timeAfter heapFreeBefore heapFreeAfter detectedCollisions ] for "
                        + ImmortalEntry.recordedRuns + " recorded detector runs, in ns");
        }
        devices.Console.println("=====DETECTOR-STATS-START-BELOW====");
        for (int i = 0; i < ImmortalEntry.recordedRuns; i++) {
            devices.Console.print(ImmortalEntry.timesBefore[i]);
            devices.Console.print(space);
            devices.Console.print(ImmortalEntry.timesAfter[i]);
            devices.Console.print(space);
            devices.Console.print(ImmortalEntry.detectedCollisions[i]);
            devices.Console.print(space);
            devices.Console.print(ImmortalEntry.suspectedCollisions[i]);
            devices.Console.print(triZero);
            devices.Console.println(i);
        }

        devices.Console.println("=====DETECTOR-STATS-END-ABOVE====");

        devices.Console.println("Generated frames: " + Constants.MAX_FRAMES);
        devices.Console.println("Received (and measured) frames: " + ImmortalEntry.recordedRuns);
        devices.Console.println("Frame not ready event count (in detector): " + ImmortalEntry.frameNotReadyCount);
        devices.Console.println("Frames dropped due to full buffer in detector: " + ImmortalEntry.droppedFrames);
        devices.Console.println("Frames processed by detector: " + ImmortalEntry.framesProcessed);
        // devices.Console.println("Detector stop indicator set: "
        // + ImmortalEntry.persistentDetectorScopeEntry.stop);
        devices.Console.println("Reported missed detector periods (reported by waitForNextPeriod): "
                + ImmortalEntry.reportedMissedPeriods);
        devices.Console.println("Detector first release was scheduled for: "
                + NanoClock.asString(ImmortalEntry.detectorFirstRelease));
        // heap measurements
        Simulator.dumpStats();

        // detector release times
        if (Constants.DETECTOR_RELEASE_STATS != "") {
            devices.Console.println("=====DETECTOR-RELEASE-STATS-START-BELOW====");
            for (int i = 0; i < ImmortalEntry.recordedDetectorReleaseTimes; i++) {
                devices.Console.print(ImmortalEntry.detectorReleaseTimes[i]);
                devices.Console.print(space);
                devices.Console.print(i * Constants.DETECTOR_PERIOD * 1000000L + ImmortalEntry.detectorReleaseTimes[0]);
                devices.Console.print(space);
                devices.Console.print(ImmortalEntry.detectorReportedMiss[i] ? 1 : 0);
                devices.Console.print(space);
                devices.Console.println(i);
            }
            devices.Console.println("=====DETECTOR-RELEASE-STATS-END-ABOVE====");
        }
    }

}
