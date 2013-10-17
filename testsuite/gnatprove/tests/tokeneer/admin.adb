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
is pragma SPARK_Mode (On);

   function RolePresent (TheAdmin : T) return PrivTypes.PrivilegeT is
     (TheAdmin.RolePresent);

   MaxDataLength : constant Positive := 18;
   subtype DataLengthT is Natural range 0 .. MaxDataLength;
   subtype DataI is Positive range 1..MaxDataLength;
   subtype DataTextT is String(DataI);

   type DataT is
      record
         Length : DataLengthT;
         MinMatchLength : DataI;
         Text   : DataTextT;
      end record;

   type OpToKeyedT is array(OpT) of DataT;
   OpToKeyed : constant OpToKeyedT := OpToKeyedT'
     (ArchiveLog       =>
        DataT'(Length         => 11,
               MinMatchLength => 7,
               Text           => "ARCHIVE LOG       "),
      UpdateConfigData =>
        DataT'(Length         => 18,
               MinMatchLength => 6,
               Text           => "UPDATE CONFIG DATA"),
      OverrideLock     =>
        DataT'(Length         => 13,
               MinMatchLength => 8,
               Text           =>"OVERRIDE LOCK     "),
      ShutdownOp       =>
        DataT'(Length         => 8,
               MinMatchLength => 8,
               Text           => "SHUTDOWN          "));


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
   -- IsPresent
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function IsPresent (TheAdmin : T) return Boolean is
     (TheAdmin.RolePresent /= PrivTypes.UserOnly);

   ------------------------------------------------------------------
   -- OpIsAvailable
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function OpIsAvailable (TheAdmin : T;
                           KeyedOp  : Keyboard.DataT) return OpAndNullT
   is
      TheOp   : OpAndNullT := NullOp;
      Matched : Boolean;
   begin
      --# assert TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT and
      --#        TheOp = NullOp;
      pragma Assert (TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT and then
                     TheOp = NullOp);
      for Op in OpT loop
         --# assert OpT'First <= Op and
         --#        Op <= OpT'Last and
         --#        TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT and
         --#        TheOp = NullOp;
         pragma Loop_Invariant
           (OpT'First <= Op and then
            Op <= OpT'Last and then
            TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT and then
            TheOp = NullOp);
         if KeyedOp.Length >= OpToKeyed(Op).MinMatchLength and
           KeyedOp.Length <=  OpToKeyed(Op).Length then
            --# assert Op in OpT and
            --#        KeyedOp.Length in DataI and
            --#        TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT and
            --#        TheOp = NullOp;
            pragma Assert (Op in OpT and then
                           KeyedOp.Length in DataI and then
                           TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT
                           and then
                           TheOp = NullOp);
            -- could have a match
            -- check to point of match
            Matched := True;
            for I in DataI range 1 .. KeyedOp.Length loop
               --# assert Op in OpT and
               --#        I in DataI and
               --#        I <= KeyedOp.Length and
               --#        KeyedOp.Length in DataI and
               --#        KeyedOp = KeyedOp% and
               --#        TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT and
               --#        TheOp = NullOp;
               pragma Loop_Invariant
                 (Op in OpT and then
                  I in DataI and then
                  I <= KeyedOp.Length and then
                  KeyedOp.Length in DataI and then
                  TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT and then
                  TheOp = NullOp);
               if OpToKeyed(Op).Text(I) /= KeyedOp.Text(I) then
                  Matched := False;
                  exit;
               end if;
            end loop;
         else
            Matched := False;
         end if;
         if Matched then

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
   -- IsDoingOp
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function IsDoingOp (TheAdmin : T) return Boolean
   is
      (TheAdmin.CurrentOp /= NullOp);

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

   function TheCurrentOp (TheAdmin : T) return OpT
   is
      (TheAdmin.CurrentOp);

   ------------------------------------------------------------------
   -- SecurityOfficerIsPresent
   --
   -- Description:
   --    Returns true if a Security Officer is present
   --
   -- traceunit : C.Admin.SecurityOfficerIsPresent
   -- traceto   : FD.Interfac.UpdateScreen
   ------------------------------------------------------------------

   function SecurityOfficerIsPresent (TheAdmin : T) return Boolean
   is
      (TheAdmin.RolePresent = PrivTypes.SecurityOfficer);

end Admin;
