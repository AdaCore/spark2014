with Debug_IO;

with Ada.Numerics;

with Formal.Numerics.Elementary_Functions;
use Formal.Numerics.Elementary_Functions;

with Spaces.Positions;
use Spaces.Positions;
with Spaces.Poses;
use Spaces.Poses;

package body Algorithm is

   pragma Unevaluated_Use_Of_Old (Allow);
   --  To allow uses of Var.Component'Loop_Entry on the right of "and then"
   --  in loop invariants.

   use Debug_IO;
   use Robot_Iface;

   use Gap_Vectors;
   use type Ada.Containers.Count_Type;

   gDebug : constant Integer := -1;

   M_PI : constant := Ada.Numerics.Pi;

   function limit (a, min, max : Float) return Float
   with
     Pre => min <= max,
     Post => limit'Result in min .. max;

   function limit (a, min, max : Float) return Float is
   begin
      if a < min then
         return min;
      elsif a > max then
         return max;
      else
         return a;
      end if;
   end limit;

   procedure Create (Robot : Robot_Iface.Proxy) is
   begin
      if gDebug >= 0 then
         Put_Line ("Starting SND driver 3.0 ...");

         Put ("Robot radius: ");
         Put (Float'Image (Robot.robot_radius));
         Put ("; obstacle_avoid_dist ");
         Put (Float'Image (Robot.obstacle_avoid_dist));
         New_Line;

         Put ("Pos tol: ");
         Put (Float'Image (Robot.goal_position_tol));
         Put ("; angle tol ");
         Put (Float'Image (Robot.goal_angle_tol));
         New_Line;

         Put_Line ("SND driver ready");

         New_Line;
         Put ("Robot at ");
         Put (Float'Image (GetXPos (Robot)));
         Put (", ");
         Put_Line (Float'Image (GetYPos (Robot)));
         New_Line;
      end if;
   end Create;

   function isFilterClear
     (scans         : Laser_Scans;
      testBearing   : Angle;
      width         : Float;
      forwardLength : Float;
      bDoRearCheck  : Boolean)
      return Boolean
   is
      pragma  Spark_Mode (On);  -- Trigonometric functions return non-zeros.
   begin
      for I in Laser_Scans'Range
      loop

         declare -- scans(i).second in 0.0 .. 2.0*Pi
            deltaAngle : constant Float := alDiff (scans (I).second, testBearing);
         begin
            -- deltaAngle in (-Pi;+Pi>
            if abs (deltaAngle) > M_PI / 2.0 then
               -- Semi-circle behind sensor
               if bDoRearCheck and then scans (I).first < width / 2.0 then
                  if gDebug > 7 then
                     Put ("  Filter:  obstacle at ");
                     Put (Print (scans (I).second));
                     Put_Line (" in rear semi-circle");
                  end if;
                  return False;
               end if;
            else
               if width /= 0.0 or else forwardLength /= 0.0 then
                  declare
                     -- Rectangle in front of robot; deltaAngle in <-Pi/2.0;+Pi/2.0>
                     --d1 : constant Float := abs((width/2.0)/sin(deltaAngle));   -- (deltaAngle -> 0.0) => (d1 -> +Inf)
                     --d2 : constant Float := abs(forwardLength/cos(deltaAngle));
                     d : Float;
                  begin
                     if abs (deltaAngle) < Arctan (abs (width) / 2.0, abs (forwardLength)) then
                        d := abs (forwardLength / Cos (deltaAngle));
                     else
                        d := abs ((width / 2.0) / Sin (deltaAngle));
                     end if;

                     if scans (I).first < d then
                        if gDebug > 7 then
                           Put ("  Filter: obstacle at ");
                           Put (Print (scans (I).second));
                           Put_Line (" in front rectangle");
                        end if;
                        return False;
                     end if;
                  end;
               end if;
            end if;
         end;
      end loop;

      return True;

   end isFilterClear;

   function isRisingGapSafe
     (This      : Controller;
      risingGap : Gap)
      return Boolean
   is
      pragma  Spark_Mode (On);  -- PROVED.
   begin
      --  TODO: only checks if point creating gap is to close to obstacle on other side ...
      --  does not guarantee safe passage through gap

      declare
         posGapCorner : constant Position := Create (risingGap.distance, risingGap.bearing);
      begin

         for I in This.laserScan'Range
         loop

            declare
               deltaAngle : constant Float := Float (risingGap.iDir) * alDiff (This.laserScan (I).second, risingGap.bearing);
            begin

               if deltaAngle > 0.0 and then deltaAngle < M_PI / 2.0 then
                  if This.laserScan (I).first < This.robot.max_Range - 0.01 then
                     if dist (posGapCorner, Create (This.laserScan (I).first, This.laserScan (I).second)) < This.robot.min_gap_width then
                        if gDebug > 4 then
                           Put ("    Gap at ");
                           Put (Print (risingGap.bearing));
                           Put (" ruled unsafe by obstacle at ");
                           Put_Line (Print (This.laserScan (I).second));
                        end if;
                        return False;
                     end if;
                  end if;
               end if;
            end;
         end loop;

      end;

      return True;

   end isRisingGapSafe;

   procedure buildGapVector (gapVec : in out List;
                             laserscan : Laser_Scans;
                             robotRadius : Formal.Numerics.Positive_Float;
                             minGapWidth : Formal.Numerics.Positive_Float;
                             fMaxRange : Formal.Numerics.Positive_Float
                            ) is
      pragma  Spark_Mode (On);  --  PROVED (except Capacity assert); requires --proof=then_split.
      rayR, rayL : Laser_Scan_Data;
   begin
      pragma Assert (gapVec.Capacity = Max_Gaps);

      Clear (gapVec);

      --  pragma Assert(Length(This.gapVec) = 0);

      --  Right edge of scan is right gap
      rayR := laserscan (laserscan'Last);
      rayL := laserscan (laserscan'First);

      declare
         dist : constant Float := (rayR.first * rayR.first) + (rayL.first * rayL.first) - 2.0 * rayR.first * rayL.first *  Cos (ccwDiff (rayR.second, rayL.second));
      begin
         if dist >= minGapWidth then
            Append (gapVec, Create (rayL.second, -robotRadius, -1));
         end if;
      end;

      pragma  Assert_And_Cut (gapVec.Capacity = Max_Gaps and then
                            Length (gapVec) <= 1);

      for I in laserscan'First + 1 .. laserscan'Last - 1
      loop
         pragma Loop_Invariant (gapVec.Capacity = Max_Gaps and then
                               Length (gapVec) < Ada.Containers.Count_Type (I));
         rayR := rayL;
         rayL := laserscan (I);

         declare
            dist : constant Float := rayL.first - rayR.first;
         begin

            if (dist >= minGapWidth) or else (rayL.first = fMaxRange and then rayR.first < fMaxRange) then
               Append (gapVec, Create (rayR.second, rayR.first, -1));
            elsif (dist <= -minGapWidth) or else (rayR.first = fMaxRange and then rayL.first < fMaxRange) then
               Append (gapVec, Create (rayL.second, rayL.first, +1));
            end if;

         end;

      end loop;

      --  Left edge of scan is a left gap
      rayR := laserscan (laserscan'Last);
      rayL := laserscan (laserscan'First);

      declare
         dist : constant Float := (rayR.first * rayR.first) + (rayL.first * rayL.first) - 2.0 * rayR.first * rayL.first *  Cos (ccwDiff (rayR.second, rayL.second));
      begin

         if dist >= minGapWidth then
            Append (gapVec, Create (rayR.second, -robotRadius, 1));
         end if;
      end;

   end buildGapVector;

   procedure removeDuplicateGaps (This : in out Controller) is
      pragma  Spark_Mode (On);  --  PROVED.

      procedure forwardScan (This : in out Controller)
      with
        Post => This.robot.robot_radius = This.robot.robot_radius'Old;

      procedure backwardScan (This : in out Controller)
      with
        Post => This.robot.robot_radius = This.robot.robot_radius'Old;

      procedure forwardScan (This : in out Controller) is
         iterR, iterL : Gap_Vectors.Cursor;
      begin
         iterL := First (This.gapVec);
         iterR := iterL;
         Next (This.gapVec, iterL);
         while iterL /= No_Element and then iterR /= No_Element and then Length (This.gapVec) > 1
         loop
            pragma Loop_Invariant (
                                  Has_Element (This.gapVec, iterR) and then
                                  Has_Element (This.gapVec, iterL) and then
                                  iterL = Next (This.gapVec, iterR) and then
                                  This.robot.robot_radius = This.robot.robot_radius'Loop_Entry
                                 );
            pragma Loop_Variant (Decreases => Last_Index (This.gapVec) - To_Index (iterL));
            if ccwDiff (Element (This.gapVec, iterR).bearing, Element (This.gapVec, iterL).bearing) < 2.0 * This.robot.scan_Res and then
              Element (This.gapVec, iterL).iDir = 1 and then Element (This.gapVec, iterR).iDir = 1
            then
               if gDebug > 4 then
                  Put ("    Removed duplicate gap at ");
                  Put_Line (Print (Element (This.gapVec, iterR).bearing));
               end if;

               --  Deleting the element pointed by iterR also sets iterR to
               --  No_Element, which is not read afterwards.
               pragma Warnings (Off, "unused assignment to ""iterR""");
               if iterR = First (This.gapVec) then
                  Delete (This.gapVec, iterR);
                  iterL := First (This.gapVec);
               else
                  iterL := Previous (This.gapVec, iterR);
                  Delete (This.gapVec, iterR);
                  Next (This.gapVec, iterL);
               end if;
               pragma Warnings (On, "unused assignment to ""iterR""");
            end if;

            iterR := iterL;
            Next (This.gapVec, iterL);
         end loop;

         --  This does not speed things up.
         --pragma Assert_And_Cut(if iterR /= No_Element then Has_Element(This.gapVec, iterR));

         if iterR /= No_Element and then Length (This.gapVec) > 1 then
            iterL := First (This.gapVec);

            if ccwDiff (Element (This.gapVec, iterR).bearing, Element (This.gapVec, iterL).bearing) < 2.0 * This.robot.scan_Res and then
              Element (This.gapVec, iterL).iDir = 1 and then Element (This.gapVec, iterR).iDir = 1
            then
               if gDebug > 4 then
                  Put ("    Removed duplicate gap at ");
                  Put_Line (Print (Element (This.gapVec, iterR).bearing));
               end if;
               --  Deleting the element pointed by iterR also sets iterR to
               --  No_Element, which is not read afterwards.
               pragma Warnings (Off, "unused assignment to ""iterR""");
               Delete (This.gapVec, iterR);
               pragma Warnings (On, "unused assignment to ""iterR""");
            end if;
         end if;
      end forwardScan;

      procedure backwardScan (This : in out Controller) is
         riterR, riterL : Gap_Vectors.Cursor; --  reverse iterators.
      begin
         riterR := Last (This.gapVec);
         riterL := riterR;
         Previous (This.gapVec, riterR);
         while riterL /= No_Element and then riterR /= No_Element and then Length (This.gapVec) > 1
         loop
            pragma Loop_Invariant (
                                  Has_Element (This.gapVec, riterR) and then
                                  Has_Element (This.gapVec, riterL) and then
                                  riterL = Next (This.gapVec, riterR) and then
                                  This.robot.robot_radius = This.robot.robot_radius'Loop_Entry
                                 );
            pragma Loop_Variant (Decreases => To_Index (riterL));
            if ccwDiff (Element (This.gapVec, riterR).bearing, Element (This.gapVec, riterL).bearing) < 2.0 * This.robot.scan_Res and then
              Element (This.gapVec, riterL).iDir = -1 and then Element (This.gapVec, riterR).iDir = -1
            then
               if gDebug > 4 then
                  Put ("    Removed duplicate gap at ");
                  Put_Line (Print (Element (This.gapVec, Previous (This.gapVec, riterL)).bearing));
               end if;
               --  Deleting the element pointed by riterL also sets riterL to
               --  No_Element, which is not read afterwards.
               pragma Warnings (Off, "unused assignment to ""riterL""");
               Delete (This.gapVec, riterL);
               pragma Warnings (On, "unused assignment to ""riterL""");
            end if;

            riterL := riterR;
            Previous (This.gapVec, riterR);
         end loop;

         if riterL /= First (This.gapVec) and then Length (This.gapVec) > 1 then
            riterR := Last (This.gapVec);

            if ccwDiff (Element (This.gapVec, riterR).bearing, Element (This.gapVec, riterL).bearing) < 2.0 * This.robot.scan_Res and then
              Element (This.gapVec, riterL).iDir = -1 and then Element (This.gapVec, riterR).iDir = -1
            then
               if gDebug > 4 then
                  Put ("    Removed duplicate gap at ");
                  Put_Line (Print (Element (This.gapVec, Previous (This.gapVec, riterL)).bearing));
               end if;
               --  Deleting the element pointed by riterL also sets riterL to
               --  No_Element, which is not read afterwards.
               pragma Warnings (Off, "unused assignment to ""riterL""");
               Gap_Vectors.Delete (This.gapVec, riterL);
               pragma Warnings (On, "unused assignment to ""riterL""");
            end if;
         end if;
      end backwardScan;

   begin

      forwardScan (This);
      backwardScan (This);

   end removeDuplicateGaps;

   function findBestValley
     (This       : Controller;
      distToGoal : Position)
     return Valley_Option
   is
      pragma  Spark_Mode (On);  --  PROVED (except Capacity assert).

      subtype Existing_Gap_ID is Gap_ID range Gap_ID'First .. Gap_ID (Length (This.gapVec));

      type Gap_ID_Pair (Opt : Option := O_NONE) is record
         case Opt is
         when O_NONE =>
            null;
         when O_SOME =>
            rising, other : Existing_Gap_ID;
         end case;
      end record;

      Best_Valley_IDS : Gap_ID_Pair := (Opt => O_NONE);
   begin
      pragma Assert (This.gapVec.Capacity = Max_Gaps);

      for iR in Existing_Gap_ID range 1 .. Gap_ID (Length (This.gapVec))
      loop
         pragma Loop_Invariant (This.gapVec.Capacity = Max_Gaps and then
                               Length (This.gapVec) = Length (This.gapVec'Loop_Entry));

         declare
            iL : constant Existing_Gap_ID :=
              (iR mod Integer (Length (This.gapVec))) + 1;

            Candidate_Valley_IDS : Gap_ID_Pair := (Opt => O_NONE);
         begin

            if Element (This.gapVec, iR).iDir = -1 then
               if isRisingGapSafe (This, Element (This.gapVec, iR)) then
                  Candidate_Valley_IDS := (Opt => O_SOME,
                                           rising => iR, other => iL);
               else
                  if gDebug > 2 then
                     Put (" Potential rising gap at ");
                     Put (Print (Element (This.gapVec, iR).bearing));
                     Put_Line (" is not safe");
                  end if;
               end if;
            end if;

            if Element (This.gapVec, iL).iDir = 1 then
               if isRisingGapSafe (This, Element (This.gapVec, iL)) then
                  if Candidate_Valley_IDS.Opt = O_SOME then
                     --  Both gaps are rising, pick one closer to goal

                     --  Angular proximity
                     if abs (alDiff (Element (This.gapVec, iL).bearing,  bearing (distToGoal)))
                       < abs (alDiff (Element (This.gapVec, Candidate_Valley_IDS.rising).bearing,  bearing (distToGoal)))
                     then
                        Candidate_Valley_IDS := (Opt => O_SOME,
                                                 rising => iL, other => iR);
                     end if;

                     --  Physical proximity
                     --  if dist(distToGoal, Create(Element(This.gapVec,iL).distance, Element(This.gapVec,iL).bearing))  <
                     --    dist(distToGoal, Create(Element(This.gapVec,iR).distance, Element(This.gapVec,iR).bearing))
                     --  then
                     --      iRisingGap := iL;
                     --      iOtherGap := iR;
                     --  end if;
                  else
                     Candidate_Valley_IDS := (Opt => O_SOME,
                                              rising => iL, other => iR);
                  end if;
               else
                  if gDebug > 2 then
                     Put (" Potential rising gap at ");
                     Put (Print (Element (This.gapVec, iL).bearing));
                     Put_Line (" is not safe");
                  end if;
               end if;
            end if;

            if Candidate_Valley_IDS.Opt = O_SOME then
               if Best_Valley_IDS.Opt = O_SOME then
--                    pragma Assert(iBestValleyRising >= Gap_ID'First);
--                    pragma Assert(iBestValleyRising <= Integer(Length(This.gapVec)));
                  if gDebug > 4 then
                     Put ("      Checking valley with rising ");
                     Put_Line (Gap_ID'Image (Candidate_Valley_IDS.rising));

                     Put ("        Goal at ");
                     Put_Line (Print (bearing (distToGoal)));

                     Put ("        diff from rising at ");
                     Put (Print (Element (This.gapVec, Candidate_Valley_IDS.rising).bearing));
                     Put (" is ");
                     Put_Line (Float'Image (abs (alDiff (Element (This.gapVec, Candidate_Valley_IDS.rising).bearing,  bearing (distToGoal)))));

                     Put ("        diff from best at   ");
                     Put (Print (Element (This.gapVec, Best_Valley_IDS.rising).bearing));
                     Put (" is ");
                     Put_Line (Float'Image (abs (alDiff (Element (This.gapVec, Best_Valley_IDS.rising).bearing,  bearing (distToGoal)))));
                  end if;

                  --  Angular proximity
                  if abs (alDiff (Element (This.gapVec, Candidate_Valley_IDS.rising).bearing,  bearing (distToGoal)))
                    < abs (alDiff (Element (This.gapVec, Best_Valley_IDS.rising).bearing,  bearing (distToGoal)))
                  then
                     if gDebug > 3 then
                        Put ("    New best valley with rising ");
                        Put_Line (Gap_ID'Image (Candidate_Valley_IDS.rising));
                     end if;
                     Best_Valley_IDS := Candidate_Valley_IDS;
                  end if;

                  --  Physical proximity
                  --  if( distToGoal.dist( Position(gapVec[iRisingGap].distance, gapVec[iRisingGap].bearing) ) <
                  --      distToGoal.dist( Position(gapVec[iBestValleyRising].distance, gapVec[iBestValleyRising].bearing) ) )
                  --  then
                  --      iBestValleyRising := iRisingGap;
                  --      iBestValleyOther := iOtherGap;
                  --  end if;
               else
                  if gDebug > 3 then
                     Put ("    New best valley with rising ");
                     Put_Line (Gap_ID'Image (Candidate_Valley_IDS.rising));
                  end if;
                  Best_Valley_IDS := Candidate_Valley_IDS;
               end if;
            end if;
         end;
      end loop;

      if Best_Valley_IDS.Opt = O_SOME then
         if gDebug > 1 then
            Put ("  Best valley has rising gap at ");
            Put_Line (Print (Element (This.gapVec, Best_Valley_IDS.rising).bearing));
         end if;
         return (Opt => O_SOME,
                 value => Valleys.Create (
                   Element (This.gapVec, Best_Valley_IDS.rising),
                   Element (This.gapVec, Best_Valley_IDS.other)));
      else
         return (Opt => O_NONE);
      end if;

   end findBestValley;

   function ObsAvoidDelta
     (This       : Controller;
      safetyDist : Float) return Float
   is
      pragma  Spark_Mode (On);  -- PROVED.

      subtype Zero_To_One is Float range 0.0 .. 1.0;

      deltaMag : Zero_To_One;
      deltaAngle : Float;
      deltaAreaSum : Formal.Numerics.NonNegative_Float := 0.0;
      obstacleAvoidDelta : Float := 0.0;
   begin
      for I in This.laserScan'Range
      loop
         pragma Loop_Invariant (This.robot.robot_radius = This.robot.robot_radius'Loop_Entry);
         if This.laserScan (I).first <= safetyDist + This.robot.robot_radius then
            deltaMag := limit ((safetyDist + This.robot.robot_radius - This.laserScan (I).first) / safetyDist, 0.0, 1.0);
            deltaAngle := alDiff (This.driveAngle, This.laserScan (I).second + Create (M_PI));

            deltaAreaSum := deltaAreaSum + deltaMag * deltaMag;

            obstacleAvoidDelta := obstacleAvoidDelta + deltaMag * deltaMag * deltaMag * deltaAngle;
         end if;
      end loop;

      obstacleAvoidDelta := (if deltaAreaSum > 0.0
                             then obstacleAvoidDelta / deltaAreaSum
                             else 0.0);

      return obstacleAvoidDelta;

   end ObsAvoidDelta;

   procedure Step (This : in out Controller) is
      pragma  Spark_Mode (On);
      driveSpeed : Float;
      driveTurnRate : Float;
      relGoal : Pose;
      distToGoal : Position;
      distToClosestObstacle : Formal.Numerics.NonNegative_Float;
      safetyDist : Formal.Numerics.Positive_Float;

      safeRisingGapAngle, midValleyAngle : Angle := Create;
      theta : Float;
      robotPose : Pose;
      goal      : Pose;
      pBestValley : Valley_Option;
      iNumLPs   : Natural;
   begin
      --  We already checked if there are new data.

      --  update _var values
      robotPose := Create (GetXPos (This.robot), GetYPos (This.robot), Create (GetYaw (This.robot)));
      if gDebug > 2 then
         Put ("pose ");
         Put_Line (print (robotPose));
      end if;

      pragma  Assert_And_Cut (True);

      goal := Create (This.robot.goalX, This.robot.goalY, Create (This.robot.goalA));
      if gDebug > 2 then
         Put ("goal ");
         Put_Line (print (goal));
      end if;

      pragma  Assert_And_Cut (True);

      This.driveAngle := Create (0.0);
      This.obsAvoidDelta := 0.0;

      iNumLPs := Robot_Iface.GetScanCount (This.robot);

      if iNumLPs = 0 or else iNumLPs > 100000 then
         SetSpeed (This.robot, 0.0, 0.0);
         return;
      end if;

      pragma  Assert_And_Cut (True);

      for I in This.laserScan'Range loop
         This.laserScan (I).first := GetRange (This.robot, I);
         This.laserScan (I).second := Create (This.robot.scan_Res * Float (I - This.laserScan'First - iNumLPs / 2));
      end loop;

      pragma  Assert_And_Cut (True);

      relGoal := goal - robotPose;

      if gDebug > 4 then
         Put ("  Rel goal pose ");
         Put_Line (print (relGoal));
      end if;

      pragma  Assert_And_Cut (True);

      --  Goal position fulfilled, no need to continue
      if norm (pos (relGoal)) <= This.robot.goal_position_tol then
         if almostEqual (ori (robotPose), ori (goal), This.robot.goal_angle_tol) then
            if gDebug > 0 then
               Put ("Reached goal location ");
               Put (print (goal));
            end if;

            SetSpeed (This.robot, 0.0, 0.0);

            GoalReached (This.robot);

            return;
         else
            if ccwDiff (ori (robotPose), ori (goal)) < M_PI then
               driveTurnRate := Float'Min (This.robot.max_turn_rate / 2.0, ccwDiff (ori (robotPose), ori (goal)) / 3.0);
            else
               driveTurnRate := Float'Min (-This.robot.max_turn_rate / 2.0, cwDiff (ori (robotPose), ori (goal)) / 3.0);
            end if;

            SetSpeed (This.robot, 0.0, driveTurnRate);

            return;
         end if;
      end if;

      distToGoal := Create (norm (pos (relGoal)), bearing (pos (relGoal)) - ori (robotPose));

      pragma Assert (distToGoal /= Zero_Position);
      pragma Assert (This.robot.robot_radius < This.robot.max_Range);

      if gDebug > 4 then
         Put ("  Dist to goal ");
         Put_Line (print (distToGoal));
      end if;

      pragma  Assert_And_Cut (distToGoal /= Zero_Position and then This.robot.robot_radius < This.robot.max_Range);
      --  Check closest obstacle
      distToClosestObstacle := This.robot.max_Range;
      pragma Assert (distToClosestObstacle > This.robot.robot_radius);
      for I in This.laserScan'Range
      loop
         pragma Loop_Invariant (distToGoal /= Zero_Position and then distToClosestObstacle > This.robot.robot_radius);

         if This.laserScan (I).first <= This.robot.robot_radius then
            if gDebug > 0 then
               Put_Line (" Obstacle inside of robot's boundary!  Stopping");
            end if;
            SetSpeed (This.robot, 0.0, 0.0);
            return;
         end if;

         pragma Assert (This.laserScan (I).first > This.robot.robot_radius);

         if This.laserScan (I).first <= This.robot.obstacle_avoid_dist + This.robot.robot_radius then
            distToClosestObstacle := Float'Min (distToClosestObstacle, This.laserScan (I).first);
         end if;

      end loop;

      pragma  Assert_And_Cut (distToGoal /= Zero_Position and then distToClosestObstacle > This.robot.robot_radius);
      pragma Assert (This.robot.robot_radius / 10.0 <= This.robot.obstacle_avoid_dist);
      safetyDist := limit (3.0 * (distToClosestObstacle - This.robot.robot_radius), This.robot.robot_radius / 10.0, This.robot.obstacle_avoid_dist);

      --  Create list of gap/discontinuity angles
      buildGapVector (gapVec      => This.gapVec,
                     laserscan   => This.laserScan,
                     robotRadius => This.robot.robot_radius,
                     minGapWidth => This.robot.min_gap_width,
                     fMaxRange   => This.robot.max_Range);

      if gDebug > 2 then
         for I in First_Index (This.gapVec) .. Last_Index (This.gapVec)
         loop
            pragma Loop_Invariant (distToGoal /= Zero_Position and then
                                  This = This'Loop_Entry);
            Put ("  Gap at ");
            Put (Float'Image (dCastPi (Element (This.gapVec, I).bearing)));
            Put (", dir ");
            Put (iDir_t'Image (Element (This.gapVec, I).iDir));
            Put (", ");
            Put_Line (Float'Image (Element (This.gapVec, I).distance));
         end loop;
      end if;

      pragma  Assert_And_Cut (distToGoal /= Zero_Position and then distToClosestObstacle > This.robot.robot_radius);

      --  Clean up gap list, combining neighboring gaps.  Keep right most right gap, left most left gap
      removeDuplicateGaps (This);

      --  Find best valley
      pBestValley := findBestValley (This, distToGoal);

      pragma  Assert_And_Cut (distToGoal /= Zero_Position and then distToClosestObstacle > This.robot.robot_radius);

      --  Drive scenarios
      if isFilterClear (This.laserScan,
                        bearing (distToGoal),
                       This.robot.min_gap_width,
                       Float'Min (This.robot.max_Range - This.robot.robot_radius, norm (distToGoal)),
                       false)
      then
         if gDebug > 0 then
            Put_Line ("  Heading straight for goal, path is clear!");
         end if;
         if gDebug > 0 then
            Put ("   Dist to goal ");
            Put (Float'Image (norm (distToGoal)));
            Put (" angle ");
            Put (Print (bearing (distToGoal)));
         end if;
         This.driveAngle := Create (dCast (bearing (distToGoal)));
      elsif pBestValley.Opt = O_NONE then
         if gDebug > 0 then
            Put_Line ("  No where to go, turning in place");
         end if;
         This.driveAngle := Create (M_PI / 2.0);

         driveTurnRate := This.robot.max_turn_rate / 2.0;
         SetSpeed (This.robot, 0.0, driveTurnRate);
         return;
      else
         --  arctangent seems to work better in tight situations, arcsin sometimes wanted to send robot far from valley
         --  in tight situations
         declare
            safetyDeltaAngle : constant Angle := Create (Arctan (
                                                        This.robot.obstacle_avoid_dist + This.robot.robot_radius,
                                                        Float'Max (This.robot.robot_radius, pBestValley.value.risingGap.distance)));
--              safetyDeltaAngle : constant Angle := Create;
         begin
--              --Angle safetyDeltaAngle = M_PI/2;
--              --if( pBestValley->risingGap.distance > obstacleAvoidDist + robotRadius )
--              --{
--              --    safetyDeltaAngle = asin( limit((obstacleAvoidDist + robotRadius)/(pBestValley->risingGap.distance), 0.0, 1.0) );
--              --}

            if gDebug > 1 then
               Put ("    Best valley has rising at ");
               Put_Line (Print (pBestValley.value.risingGap.bearing));

               Put ("      safety delta = ");
               Put_Line (Print (safetyDeltaAngle));
            end if;

            pragma  Assert_And_Cut (distToClosestObstacle > This.robot.robot_radius and then
                                  pBestValley.Opt = O_SOME);

            safeRisingGapAngle := pBestValley.value.risingGap.bearing - Create (Float (pBestValley.value.risingGap.iDir) * dCast (safetyDeltaAngle));

            if pBestValley.value.risingGap.iDir > 0 then
               midValleyAngle := cwMean (pBestValley.value.risingGap.bearing, pBestValley.value.otherGap.bearing);
            else
               midValleyAngle := ccwMean (pBestValley.value.risingGap.bearing, pBestValley.value.otherGap.bearing);
            end if;

            pragma  Assert_And_Cut (distToClosestObstacle > This.robot.robot_radius and then
                                  pBestValley.Opt = O_SOME);

            if abs (alDiff (safeRisingGapAngle, pBestValley.value.risingGap.bearing))
              < abs (alDiff (midValleyAngle, pBestValley.value.risingGap.bearing))
            then
               This.driveAngle := safeRisingGapAngle;
            else
               This.driveAngle := midValleyAngle;
            end if;

            --if gDebug > 1
            --then
            --cout<< "    Best valley has rising at " << pBestValley->risingGap.bearing.print() << endl;
            --cout<< "      safety delta = " << safetyDeltaAngle.print() << endl;
            --cout<< "      safe rising  = " << safeRisingGapAngle.print() << endl;
            --cout<< "      mid valley   = " << midValleyAngle.print() << endl;
            --end if;
         end;
      end if;

      pragma  Assert_And_Cut (distToClosestObstacle > This.robot.robot_radius);

      --  Consider nearby obstacles
      This.obsAvoidDelta := ObsAvoidDelta (This, safetyDist);

      if gDebug > 2 then
         Put (" Starting drive angle ");
         Put (Print (This.driveAngle));
         Put_Line (Float'Image (dCastPi (This.driveAngle)));
      end if;

      pragma  Assert_And_Cut (distToClosestObstacle > This.robot.robot_radius);

      --  Don't allow obstacles to change sign of sharp turns
      if dCastPi (This.driveAngle) > M_PI / 2.0 then
         This.driveAngle := This.driveAngle + Create (This.obsAvoidDelta);
         if dCastPi (This.driveAngle) < 0.0 then
            This.driveAngle := Create (M_PI / 2.0);
         end if;
      elsif dCastPi (This.driveAngle) < -M_PI / 2.0 then
         This.driveAngle := This.driveAngle + Create (This.obsAvoidDelta);
         if dCast (This.driveAngle) > 0.0 then
            This.driveAngle := Create (-M_PI / 2.0);
         end if;
      else
         This.driveAngle := This.driveAngle + Create (This.obsAvoidDelta);
      end if;

      pragma  Assert_And_Cut (distToClosestObstacle > This.robot.robot_radius);

      if dCast (This.driveAngle) > M_PI then
         theta := dCast (This.driveAngle) - 2.0 * M_PI;
      else
         theta := dCast (This.driveAngle);
      end if;

      pragma  Assert_And_Cut (distToClosestObstacle > This.robot.robot_radius);

      if gDebug > 2 then
         Put (" Drive angle : ");
         Put (Print (This.driveAngle));

         Put (" from mid ");
         Put (Print (midValleyAngle));
         Put (", safe rising ");
         Put (Print (safeRisingGapAngle));
         Put (", and ");
         Put (Float'Image (This.obsAvoidDelta));
         Put_Line (" obs delta");
      end if;

      pragma  Assert_And_Cut (distToClosestObstacle > This.robot.robot_radius);

      if gDebug > 2 then
         Put (" Theta ");
         Put (Float'Image (theta));
         Put (" , ");
         Put_Line (Float'Image (dCastPi (This.driveAngle)));
      end if;

      pragma  Assert_And_Cut (distToClosestObstacle > This.robot.robot_radius);

      theta := limit (theta, -M_PI / 2.0, M_PI / 2.0);

      driveTurnRate := This.robot.max_turn_rate * (2.0 * theta / M_PI);
      driveTurnRate := driveTurnRate * limit (Sqrt (norm (distToGoal)), 0.2, 1.0);
      pragma Assert (distToClosestObstacle - This.robot.robot_radius > 0.0);
      pragma Assert (This.robot.obstacle_avoid_dist > 0.0); pragma Assert ((distToClosestObstacle - This.robot.robot_radius) > 0.0 and then This.robot.obstacle_avoid_dist > 0.0);
      pragma Assert ((distToClosestObstacle - This.robot.robot_radius) / This.robot.obstacle_avoid_dist > 0.0);
      pragma Assert ((distToClosestObstacle - This.robot.robot_radius) / This.robot.obstacle_avoid_dist >= 0.0);
      driveTurnRate := driveTurnRate * limit (Sqrt ((distToClosestObstacle - This.robot.robot_radius) / This.robot.obstacle_avoid_dist), 0.5, 1.0);

      theta := limit (theta, -M_PI / 4.0, M_PI / 4.0);

      driveSpeed := This.robot.max_speed;
      driveSpeed := driveSpeed * limit (Sqrt (norm (distToGoal)), 0.0, 1.0);
      driveSpeed := driveSpeed * limit (Sqrt ((distToClosestObstacle - This.robot.robot_radius) / This.robot.obstacle_avoid_dist), 0.0, 1.0);
      driveSpeed := driveSpeed * limit ((M_PI / 6.0 - abs (theta)) / (M_PI / 6.0), 0.0, 1.0);

      SetSpeed (This.robot, driveSpeed, driveTurnRate);

      if gDebug > 0 then
         Put (" Drive commands: ");
         Put (Float'Image (driveSpeed));
         Put (", ");
         Put_Line (Float'Image (driveTurnRate));
      end if;

   end Step;

end Algorithm;
