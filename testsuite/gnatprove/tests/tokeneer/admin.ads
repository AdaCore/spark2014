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
   type OpAndNullT is
     (NullOp,
      ArchiveLog,
      UpdateConfigData,
      OverrideLock,
      ShutdownOp);

   subtype OpT is OpAndNullT range ArchiveLog .. ShutdownOp;

   type T is private;

   --  Returns the role of TheAdmin.
   function RolePresent (TheAdmin : T) return PrivTypes.PrivilegeT
     with Global     => null,
          Ghost;

   ------------------------------------------------------------------
   -- IsDoingOp
   --
   -- Description:
   --    Returns true if an admin operation is in progress
   --
   -- traceunit : C.Admin.IsDoingOp
   -- traceto   : FD.Admin.AdminIsDoingOp
   ------------------------------------------------------------------
   function IsDoingOp (TheAdmin : T) return Boolean
     with Global => null;

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
     with Global => null,
          Pre    => IsDoingOp (TheAdmin);

   ------------------------------------------------------------------
   -- Str_Comp
   --
   -- Description:
   --    Returns true if the KeyedOp matches the current Operation
   ------------------------------------------------------------------
   function Str_Comp (KeyedOp : Keyboard.DataT;
                      Op      : OpT)
                     return Boolean
     with Global => null;

   --------------------------------------------------------------------
   -- AllowedOp
   --
   -- Description:
   --    Returns true if Op is allowed for the current Admin
   --------------------------------------------------------------------
   function AllowedOp (TheAdmin : T;
                       Op       : OpT)
                      return Boolean
     with Global => null,
          Pre    => IsPresent (TheAdmin);

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Description:
   --    Returns true if an administrator is present
   --
   -- traceunit : C.Admin.IsPresent
   -- traceto   : FD.Admin.AdminIsPresent
   ------------------------------------------------------------------
   function IsPresent (TheAdmin : T) return Boolean
     with Global => null;

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
     with Global  => null,
          Depends => (TheAdmin => null),
          Post    => not IsPresent(TheAdmin)
                       and not IsDoingOp(TheAdmin);

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
                           KeyedOp  : Keyboard.DataT)
                          return OpAndNullT
     with Global => null,
          Pre    => IsPresent (TheAdmin),
          Post   => (for some Op in Opt => Str_Comp (KeyedOp, Op)
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
     with Global  => null,
          Depends => (TheAdmin => Role),
          Post    => RolePresent (TheAdmin) = Role
                       and not IsDoingOp (TheAdmin)
                       and IsPresent (TheAdmin);

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
     with Global => null,
          Post   => not IsPresent (TheAdmin)
                      and not IsDoingOp (TheAdmin);

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
     with Global  => null,
          Depends => (TheAdmin => (TheAdmin, Op)),
          Pre     => IsPresent (TheAdmin)
                       and not IsDoingOp (TheAdmin),
          Post    => RolePresent (TheAdmin) = RolePresent (TheAdmin'Old)
                       and IsPresent (TheAdmin)
                       and IsDoingOp (TheAdmin)
                       and TheCurrentOp (TheAdmin) = Op;

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
     with Global  => null,
          Depends => (TheAdmin => TheAdmin),
          Pre     => IsPresent (TheAdmin),
          Post    => not IsDoingOp (TheAdmin)
                       and RolePresent (TheAdmin) = RolePresent (TheAdmin'Old)
                       and IsPresent (TheAdmin);

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
     with Global => null;

private
   type T is record
      RolePresent : PrivTypes.PrivilegeT;
      CurrentOp   : OpAndNullT;
   end record;

   type AvailOpsT is array (OpT) of Boolean;
   type PrivToAvailOpsT is array (PrivTypes.AdminPrivilegeT) of AvailOpsT;

   IsAvailable : constant PrivToAvailOpsT :=
     PrivToAvailOpsT'
       (PrivTypes.Guard           => AvailOpsT'(OverrideLock => True,
                                                others       => False),
        PrivTypes.AuditManager    => AvailOpsT'(ArchiveLog => True,
                                                others     => False),
        PrivTypes.SecurityOfficer => AvailOpsT'(UpdateConfigData => True,
                                                ShutdownOp       => True,
                                                others           => False));

   function RolePresent (TheAdmin : T) return PrivTypes.PrivilegeT is
     (TheAdmin.RolePresent);

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function IsPresent (TheAdmin : T) return Boolean is
     (TheAdmin.RolePresent in PrivTypes.AdminPrivilegeT);

   ------------------------------------------------------------------
   -- IsDoingOp
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function IsDoingOp (TheAdmin : T) return Boolean is
      (TheAdmin.CurrentOp in OpT);

   --------------------------------------------------------------------
   -- AllowedOp
   --
   -- Description:
   --    Returns the Operation that is allowed for the current Admin
   --------------------------------------------------------------------
   function AllowedOp (TheAdmin : T;
                       Op       : OpT)
                      return Boolean
   is
     (IsAvailable(TheAdmin.RolePresent)(Op));

end Admin;
