------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              S P A R K _ D E F I N I T I O N - V I O L A T I O N         --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2020-2020, AdaCore                     --
--                Copyright (C) 2014-2020, Altran UK Limited                --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Errout;   use Errout;
with Namet;    use Namet;
with Restrict; use Restrict;
with Rident;   use Rident;
with Sem_Prag; use Sem_Prag;
with Tbuild;   use Tbuild;

package body SPARK_Definition.Violations is

   ------------------------------
   -- Add_Violation_Root_Cause --
   ------------------------------

   procedure Add_Violation_Root_Cause (N : Node_Id; Msg : String) is
   begin
      Violation_Root_Cause.Include (N, Msg);
      Last_Violation_Root_Cause_Node := N;
   end Add_Violation_Root_Cause;

   procedure Add_Violation_Root_Cause (N : Node_Id; From : Node_Id) is
      Msg : constant String := Get_Violation_Root_Cause (From);
   begin
      if Msg /= "" then
         Add_Violation_Root_Cause (N, Msg);
      end if;
   end Add_Violation_Root_Cause;

   -------------------------------
   -- GNATprove_Tasking_Profile --
   -------------------------------

   --  Check that the current settings match those in
   --  Sem_Prag.Set_Ravenscar_Profile.
   --  ??? Older versions of Ada are also supported to ease reuse once this
   --  code is moved to Restrict package.

   function GNATprove_Tasking_Profile return Boolean is
      function Restriction_No_Dependence (Unit : Node_Id) return Boolean;
      --  Check if restriction No_Dependence is set for Unit.

      -------------------------------
      -- Restriction_No_Dependence --
      -------------------------------

      function Restriction_No_Dependence (Unit : Node_Id) return Boolean is
         function Same_Unit (U1, U2 : Node_Id) return Boolean;
         --  Returns True iff U1 and U2 represent the same library unit.
         --  Used for handling of No_Dependence => Unit restriction case.
         --  ??? This duplicates the code from Restrict package.

         ---------------
         -- Same_Unit --
         ---------------

         function Same_Unit (U1, U2 : Node_Id) return Boolean is
         begin
            if Nkind (U1) = N_Identifier and then Nkind (U2) = N_Identifier
            then
               return Chars (U1) = Chars (U2);

            elsif Nkind (U1) in N_Selected_Component | N_Expanded_Name
              and then
                Nkind (U2) in N_Selected_Component | N_Expanded_Name
            then
               return Same_Unit (Prefix (U1), Prefix (U2))
                 and then
                   Same_Unit (Selector_Name (U1), Selector_Name (U2));
            else
               return False;
            end if;
         end Same_Unit;

      --  Start of processing for Restriction_No_Dependence

      begin
         --  Loop to look for entry

         for J in No_Dependences.First .. No_Dependences.Last loop

            --  Entry is in table

            if Same_Unit (Unit, No_Dependences.Table (J).Unit) then
               return True;
            end if;

         end loop;

         --  Entry is not in table

         return False;
      end Restriction_No_Dependence;

      --  Local variables

      Profile : Profile_Data renames Profile_Info (Jorvik);
      --  A minimal settings required for tasking constructs to be allowed
      --  in SPARK.

      Parent_Unit : Node_Id;
      Child_Unit  : Node_Id;
      --  For constructing names of restricted units

   --  Start of processing for GNATprove_Tasking_Profile

   begin
      if Ravenscar_Profile_Cached then
         return Ravenscar_Profile_Result;

      else
         Ravenscar_Profile_Result := True;
         Ravenscar_Profile_Cached := True;

         --  pragma Task_Dispatching_Policy (FIFO_Within_Priorities)

         if Task_Dispatching_Policy /= 'F' then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         --  pragma Locking_Policy (Ceiling_Locking)

         if Locking_Policy /= 'C' then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         --  pragma Detect_Blocking

         if not Detect_Blocking then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         declare
            R : Restriction_Flags  renames Profile.Set;
            V : Restriction_Values renames Profile.Value;
         begin
            for J in R'Range loop
               if R (J)
                 and then (Restrictions.Set (J) = False
                           or else Restriction_Warnings (J)
                           or else
                             (J in All_Parameter_Restrictions
                              and then Restrictions.Value (J) > V (J)))
               then
                  --  Any code that complies with the Simple_Barriers
                  --  restriction (which is required by the Ravenscar
                  --  profile) also complies with Pure_Barriers (which is
                  --  its relaxed variant required by the Jorvik profile).

                  if J = Pure_Barriers
                    and then Restrictions.Set (Simple_Barriers)
                  then
                     null;

                  --  Likewise, No_Implicit_Task_Allocations of the Ravenscar
                  --  profile implies No_Implicit_Task_Allocations and
                  --  No_Implicit_Protected_Object_Allocations of the Jorvik
                  --  profile.

                  elsif J in No_Implicit_Task_Allocations
                           | No_Implicit_Protected_Object_Allocations
                    and then Restrictions.Set (No_Implicit_Heap_Allocations)
                  then
                     null;

                  else
                     Ravenscar_Profile_Result := False;
                     return False;
                  end if;
               end if;
            end loop;
         end;

         --  The following No_Dependence restrictions:
         --    No_Dependence => Ada.Asynchronous_Task_Control
         --    No_Dependence => Ada.Task_Attributes
         --  are already checked by the above loop.

         --  The following restrictions were added to Ada 2005:
         --    No_Dependence => Ada.Execution_Time.Group_Budget
         --    No_Dependence => Ada.Execution_Time.Timers.

         if Ada_Version >= Ada_2005 then

            Parent_Unit := Sel_Comp ("ada", "execution_time", No_Location);
            Child_Unit  := Sel_Comp (Parent_Unit, "group_budgets");

            if not Restriction_No_Dependence (Unit => Child_Unit) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

            Child_Unit := Sel_Comp (Parent_Unit, "timers");

            if not Restriction_No_Dependence (Unit => Child_Unit) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

         end if;

         --  The following restriction was added to Ada 2012:
         --    No_Dependence => System.Multiprocessors.Dispatching_Domains.

         if Ada_Version >= Ada_2012 then

            Parent_Unit := Sel_Comp ("system", "multiprocessors", No_Location);
            Child_Unit  := Sel_Comp (Parent_Unit, "dispatching_domains");

            if not Restriction_No_Dependence (Unit => Child_Unit) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

         end if;

         return True;
      end if;
   end GNATprove_Tasking_Profile;

   ----------------------
   -- Mark_Unsupported --
   ----------------------

   procedure Mark_Unsupported
     (Msg      : String;
      N        : Node_Id;
      Cont_Msg : String := "")
   is
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      --  Define the root cause

      if Emit_Messages then
         Add_Violation_Root_Cause (N, Msg);
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
         Error_Msg_N (Msg & " is not yet supported", N);

         if Cont_Msg /= "" then
            Error_Msg_N ('\' & Cont_Msg, N);
         end if;
      end if;
   end Mark_Unsupported;

   --------------------
   -- Mark_Violation --
   --------------------

   procedure Mark_Violation
     (Msg           : String;
      N             : Node_Id;
      SRM_Reference : String := "";
      Cont_Msg      : String := "") is
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      --  Define the root cause

      if Emit_Messages then
         Add_Violation_Root_Cause (N, Msg);
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then

         if SRM_Reference /= "" then
            Error_Msg_F
              (Msg & " is not allowed in SPARK (" & SRM_Reference & ")", N);
         else
            Error_Msg_F (Msg & " is not allowed in SPARK", N);
         end if;

         if Cont_Msg /= "" then
            Error_Msg_F ('\' & Cont_Msg, N);
         end if;

         Mark_Violation_Of_SPARK_Mode (N);
      end if;
   end Mark_Violation;

   procedure Mark_Violation
     (N    : Node_Id;
      From : Entity_Id) is
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      --  Propagate the root cause to N if it is an entity

      if Emit_Messages then
         Add_Violation_Root_Cause (N, From);
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
         declare
            Root_Cause : constant String := Get_Violation_Root_Cause (From);
            Root_Msg   : constant String :=
              (if Root_Cause = "" then ""
               else " (due to " & Root_Cause & ")");
         begin
            Error_Msg_FE ("& is not allowed in SPARK" & Root_Msg, N, From);
            Mark_Violation_Of_SPARK_Mode (N);
         end;
      end if;
   end Mark_Violation;

   -------------------------------
   -- Mark_Violation_In_Tasking --
   -------------------------------

   procedure Mark_Violation_In_Tasking (N : Node_Id) is
      Msg_Prefix : constant String := "tasking in SPARK requires ";
      Msg_Suffix : constant String := " (SPARK RM 9(2))";
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      if Emit_Messages then
         Add_Violation_Root_Cause (N, "tasking configuration");
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then

         if not GNATprove_Tasking_Profile then
            Error_Msg_F (Msg_Prefix &
                           "Ravenscar profile" & Msg_Suffix, N);
         elsif not Sequential_Elaboration then
            Error_Msg_F (Msg_Prefix &
                           "sequential elaboration" & Msg_Suffix, N);
         end if;

         Mark_Violation_Of_SPARK_Mode (N);
      end if;
   end Mark_Violation_In_Tasking;

   ----------------------------------
   -- Mark_Violation_Of_SPARK_Mode --
   ----------------------------------

   procedure Mark_Violation_Of_SPARK_Mode (N : Node_Id) is
   begin
      if Present (Current_SPARK_Pragma) then
         Error_Msg_Sloc := Sloc (Current_SPARK_Pragma);

         Error_Msg_F ("\\violation of " &
                      (if From_Aspect_Specification (Current_SPARK_Pragma)
                         then "aspect"
                         else "pragma") &
                        " SPARK_Mode #", N);
      elsif Present (Current_Incomplete_Type) then
         Error_Msg_Sloc := Sloc (Current_Incomplete_Type);

         Error_Msg_FE
           ("\\access to incomplete type & is required to be in SPARK",
            N, Current_Incomplete_Type);
      else
         pragma Assert (Present (Current_Delayed_Aspect_Type));
         Error_Msg_Sloc := Sloc (Current_Delayed_Aspect_Type);

         Error_Msg_FE
           ("\\delayed type aspect on & is required to be in SPARK", N,
            Current_Delayed_Aspect_Type);
      end if;
   end Mark_Violation_Of_SPARK_Mode;

   ---------------------
   -- SPARK_Pragma_Is --
   ---------------------

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean is
     (if Present (Current_Incomplete_Type)
      or else (Present (Current_Delayed_Aspect_Type)
               and then In_SPARK (Current_Delayed_Aspect_Type))
      then Mode = Opt.On
      --  Force SPARK_Mode => On for expressions of a delayed aspects, if the
      --  type bearing this aspect was marked in SPARK, as we have assumed
      --  it when marking everything between their declaration and freezing
      --  point, so we cannot revert that. Also force it for completion of
      --  incomplete types.

      elsif Present (Current_SPARK_Pragma)
      then Get_SPARK_Mode_From_Annotation (Current_SPARK_Pragma) = Mode
      --  In the usual case where Current_SPARK_Pragma is a pragma node, get
      --  the current mode from the pragma.

      else Mode = Opt.None
      --  Otherwise there is no applicable pragma, so SPARK_Mode is None
     );

end SPARK_Definition.Violations;
