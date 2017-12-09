------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Admin
--
-- Description:
--
--
------------------------------------------------------------------
with PrivTypes;
use type PrivTypes.PrivilegeT;
with Keyboard; use Keyboard;

package body Admin
is
   MaxDataLength : constant Positive := 18;
   subtype DataLengthT is Natural range 0 .. MaxDataLength;
   subtype DataI is Positive range 1..MaxDataLength;
   subtype DataTextT is String(DataI);

   type DataT is record
      Length         : DataLengthT;
      MinMatchLength : DataI;
      Text           : DataTextT;
   end record;

   type OpToKeyedT is array(OpT) of DataT;
   OpToKeyed : constant OpToKeyedT := OpToKeyedT'
     (ArchiveLog       => DataT'(Length         => 11,
                                 MinMatchLength => 7,
                                 Text           => "ARCHIVE LOG       "),
      UpdateConfigData => DataT'(Length         => 18,
                                 MinMatchLength => 6,
                                 Text           => "UPDATE CONFIG DATA"),
      OverrideLock     => DataT'(Length         => 13,
                                 MinMatchLength => 8,
                                 Text           =>"OVERRIDE LOCK     "),
      ShutdownOp       => DataT'(Length         => 8,
                                 MinMatchLength => 8,
                                 Text           => "SHUTDOWN          "));

   ------------------------------------------------------------------
   -- Str_Comp
   --
   -- Description:
   --    Returns True if the KeyedOp matches the current Operation
   --    and False otherwise
   ------------------------------------------------------------------
   function Str_Comp (KeyedOp : Keyboard.DataT;
                      Op      : OpT)
                     return Boolean
   is
     (KeyedOp.Length >= OpToKeyed(Op).MinMatchLength and then
      KeyedOp.Length <= OpToKeyed(Op).Length and then
      (for all I in 1 .. KeyedOp.Length =>
         OpToKeyed(Op).Text(I) = KeyedOp.Text(I)));

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Init (TheAdmin :    out T)
   is
   begin
      TheAdmin := T'(RolePresent => PrivTypes.UserOnly,
                     CurrentOp   => NullOp);
   end Init;

   ------------------------------------------------------------------
   -- OpIsAvailable
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function OpIsAvailable (TheAdmin : T;
                           KeyedOp  : Keyboard.DataT)
                          return OpAndNullT
   is
      TheOp : OpAndNullT := NullOp;
   begin
      for Op in OpT loop
         pragma Loop_Invariant (TheOp = NullOp);

         if Str_Comp (KeyedOp, Op) then

            -- Matched the KeyedOp - determine if it is
            -- available, then exit
            if IsAvailable(TheAdmin.RolePresent)(Op) then
               TheOp := Op;
            end if;
            exit;
         end if;
      end loop;
      return TheOp;
   end OpIsAvailable;

   ------------------------------------------------------------------
   -- Logon
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Logon (TheAdmin :    out T;
                    Role     : in     PrivTypes.AdminPrivilegeT)
   is
   begin
      TheAdmin.RolePresent := Role;
      TheAdmin.CurrentOp   := NullOp;
   end Logon;

   ------------------------------------------------------------------
   -- Logout
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Logout (TheAdmin :    out T)
   is
   begin
      Init(TheAdmin);
   end Logout;

   ------------------------------------------------------------------
   -- StartOp
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure StartOp (TheAdmin : in out T;
                      Op       : in     OpT)
   is
   begin
      TheAdmin.CurrentOp := Op;
   end StartOp;

   ------------------------------------------------------------------
   -- FinishOp
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure FinishOp (TheAdmin : in out T)
   is
   begin
      TheAdmin.CurrentOp := NullOp;
   end FinishOp;

   ------------------------------------------------------------------
   -- TheCurrentOp
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function TheCurrentOp (TheAdmin : T) return OpT is (TheAdmin.CurrentOp);

   ------------------------------------------------------------------
   -- SecurityOfficerIsPresent
   --
   -- Description:
   --    Returns true if a Security Officer is present
   --
   -- traceunit : C.Admin.SecurityOfficerIsPresent
   -- traceto   : FD.Interfac.UpdateScreen
   ------------------------------------------------------------------
   function SecurityOfficerIsPresent (TheAdmin : T) return Boolean is
     (TheAdmin.RolePresent = PrivTypes.SecurityOfficer);

end Admin;
