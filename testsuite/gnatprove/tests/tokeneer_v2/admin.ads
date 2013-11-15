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
--    Abstract Data Types package, containing the state of
--    the administrator
--
------------------------------------------------------------------
with PrivTypes,
     Keyboard;
use PrivTypes;

package Admin is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type OpAndNullT is (
      NullOp,
      ArchiveLog,
      UpdateConfigData,
      OverrideLock,
      ShutdownOp
      );

   subtype OpT is OpAndNullT range ArchiveLog .. ShutdownOp;

   type T is private;

   --  Returns the role of TheAdmin.
   function RolePresent (TheAdmin : T) return PrivTypes.PrivilegeT
     with Convention => Ghost;

   ------------------------------------------------------------------
   -- IsDoingOp
   --
   -- Description:
   --    Returns true if an admin operation is in progress
   --
   -- traceunit : C.Admin.IsDoingOp
   -- traceto   : FD.Admin.AdminIsDoingOp
   ------------------------------------------------------------------

   function IsDoingOp (TheAdmin : T) return Boolean;

   ------------------------------------------------------------------
   -- TheCurrentOp
   --
   -- Description:
   --    Returns the current admin operation
   --
   -- traceunit : C.Admin.TheCurrentOp
   -- traceto   : C.Admin.State
   ------------------------------------------------------------------

   function TheCurrentOp (TheAdmin : T) return OpT
     with Pre => IsDoingOp (TheAdmin);

   ------------------------------------------------------------------
   -- Str_Comp
   --
   -- Description:
   --    Returns true if the KeyedOp matches the current Operation
   ------------------------------------------------------------------

   function Str_Comp
     (KeyedOp : Keyboard.DataT;
      Op      : OpT) return Boolean;

   --------------------------------------------------------------------
   -- AllowedOp
   --
   -- Description:
   --    Returns true if Op is allowed for the current Admin
   --------------------------------------------------------------------

   function AllowedOp
     (TheAdmin : T;
      Op       : OpT) return Boolean
     with Pre => IsPresent (TheAdmin);

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Description:
   --    Returns true if an administrator is present
   --
   -- traceunit : C.Admin.IsPresent
   -- traceto   : FD.Admin.AdminIsPresent
   ------------------------------------------------------------------

   function IsPresent (TheAdmin : T) return Boolean;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes the Admin state
   --
   -- traceunit : C.Admin.Init
   -- traceto   : FD.TIS.InitIDStation
   ------------------------------------------------------------------

   procedure Init (TheAdmin :    out T)
     with Depends => (TheAdmin => null),
          Post    => not IsPresent(TheAdmin)
                       and then not IsDoingOp(TheAdmin);

   ------------------------------------------------------------------
   -- OpIsAvailable
   --
   -- Description:
   --    Returns the operation literal if the keyed operation is
   --    available to the current administrator, otherwise
   --    returns NullOp.
   --
   -- traceunit : C.Admin.OpIsAvailable
   -- traceto   : FD.AdminOpIsAvailable
   ------------------------------------------------------------------

   function OpIsAvailable (TheAdmin : T;
                           KeyedOp  : Keyboard.DataT) return OpAndNullT
     with Pre  => IsPresent (TheAdmin),
          Post => (for some Op in Opt => Str_Comp (KeyedOp, Op)
                                           and AllowedOp (TheAdmin, Op)
                                           and OpIsAvailable'Result = Op)
                  xor OpIsAvailable'Result = NullOp;

   ------------------------------------------------------------------
   -- Logon
   --
   -- Description:
   --    Logs the administrator on
   --
   -- traceunit : C.Admin.Logon
   -- traceto   : FD.Admin.AdminLogon
   ------------------------------------------------------------------

   procedure Logon (TheAdmin :    out T;
                    Role     : in     PrivTypes.AdminPrivilegeT)
     with Depends => (TheAdmin => Role),
          Post    => RolePresent (TheAdmin) = Role
                       and then not IsDoingOp (TheAdmin)
                       and then IsPresent (TheAdmin);

   ------------------------------------------------------------------
   -- Logout
   --
   -- Description:
   --    Logs the administrator out
   --
   -- traceunit : C.Admin.Logout
   -- traceto   : FD.Admin.AdminLogout
   ------------------------------------------------------------------

   procedure Logout (TheAdmin :    out T)
     with Post => not IsPresent (TheAdmin)
                    and then not IsDoingOp (TheAdmin);

   ------------------------------------------------------------------
   -- StartOp
   --
   -- Description:
   --    Starts the admin op
   --
   -- traceunit : C.Admin.StartOp
   -- traceto   : FD.Admin.AdminStartOp
   ------------------------------------------------------------------

   procedure StartOp (TheAdmin : in out T;
                      Op       : in     OpT)
     with Depends => (TheAdmin => (TheAdmin, Op)),
          Pre     => IsPresent (TheAdmin)
                       and then not IsDoingOp (TheAdmin),
          Post    => RolePresent (TheAdmin) = RolePresent (TheAdmin'Old)
                       and then IsPresent (TheAdmin)
                       and then IsDoingOp (TheAdmin)
                       and then TheCurrentOp (TheAdmin) = Op;

   ------------------------------------------------------------------
   -- FinishOp
   --
   -- Description:
   --    Finishes the admin op
   --
   -- traceunit : C.Admin.FinishOp
   -- traceto   : FD.Admin.AdminFinishOp
   ------------------------------------------------------------------

   procedure FinishOp (TheAdmin : in out T)
     with Depends => (TheAdmin => TheAdmin),
          Pre     => IsPresent (TheAdmin) and then IsDoingOp (TheAdmin),
          Post    => not IsDoingOp (TheAdmin)
                       and then RolePresent (TheAdmin)
                                  = RolePresent (TheAdmin'Old)
                       and then IsPresent (TheAdmin);

   ------------------------------------------------------------------
   -- SecurityOfficerIsPresent
   --
   -- Description:
   --    Returns true if a Security Officer is present
   --
   -- traceunit : C.Admin.SecurityOfficerIsPresent
   -- traceto   : FD.Interfac.UpdateScreen
   ------------------------------------------------------------------

   function SecurityOfficerIsPresent (TheAdmin : T) return Boolean;

private
   type T is record
      RolePresent : PrivTypes.PrivilegeT;
      CurrentOp   : OpAndNullT;
   end record;

   type AvailOpsT is array (OpT) of Boolean;
   type PrivToAvailOpsT is array (PrivTypes.AdminPrivilegeT) of AvailOpsT;

   IsAvailable : constant PrivToAvailOpsT :=
     PrivToAvailOpsT'
       (PrivTypes.Guard           =>
          AvailOpsT'(OverrideLock => True, others => False),

        PrivTypes.AuditManager    =>
          AvailOpsT'(ArchiveLog => True, others => False),

        PrivTypes.SecurityOfficer =>
          AvailOpsT'
            (UpdateConfigData => True, ShutdownOp => True, others => False));

end Admin;
