------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
--
-- Modifications to proof annotations by Phil Thornley, April 2009
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

--# inherit PrivTypes,
--#         Keyboard;

package Admin
is

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

   subtype OpT is OpAndNullT range ArchiveLog..ShutdownOp;

   type T is private;

   --# function prf_rolePresent(TheAdmin : T)
   --#    return PrivTypes.PrivilegeT;

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

   function TheCurrentOp (TheAdmin : T) return OpT;
   --# pre IsDoingOp(TheAdmin);


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

   procedure Init (TheAdmin :    out T);
   --# derives TheAdmin from ;
   --# post not IsPresent(TheAdmin) and
   --#      not IsDoingOp(TheAdmin);


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
                           KeyedOp  : Keyboard.DataT) return OpAndNullT;
   --# pre IsPresent(TheAdmin);
   --# return R => (R /= NullOp -> (R = OverrideLock <->
   --#                                prf_rolePresent(TheAdmin) = PrivTypes.Guard));


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
                    Role     : in     PrivTypes.AdminPrivilegeT);
   --# derives TheAdmin from Role;
   --# post ( Role = PrivTypes.Guard <-> prf_rolePresent(TheAdmin) =
   --#                                               PrivTypes.Guard ) and
   --#      not IsDoingOp(TheAdmin) and
   --#      IsPresent(TheAdmin);


   ------------------------------------------------------------------
   -- Logout
   --
   -- Description:
   --    Logs the administrator out
   --
   -- traceunit : C.Admin.Logout
   -- traceto   : FD.Admin.AdminLogout
   ------------------------------------------------------------------

   procedure Logout (TheAdmin :    out T);
   --# derives TheAdmin from ;
   --# post not IsPresent(TheAdmin) and
   --#      not IsDoingOp(TheAdmin);


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
                      Op       : in     OpT);
   --# derives TheAdmin from TheAdmin,
   --#                       Op;
   --# pre  IsPresent(TheAdmin);
   --# post (( Op = OverrideLock <->
   --#          prf_rolePresent(TheAdmin~) = PrivTypes.Guard ) ->
   --#         ( Op = OverrideLock <->
   --#            prf_rolePresent(TheAdmin) = PrivTypes.Guard )) and
   --#      TheCurrentOp(TheAdmin) = Op and
   --#      IsDoingOp(TheAdmin) and
   --#      prf_rolePresent(TheAdmin) = prf_rolePresent(TheAdmin~) and
   --#      IsPresent(TheAdmin);



   ------------------------------------------------------------------
   -- FinishOp
   --
   -- Description:
   --    Finishes the admin op
   --
   -- traceunit : C.Admin.FinishOp
   -- traceto   : FD.Admin.AdminFinishOp
   ------------------------------------------------------------------

   procedure FinishOp (TheAdmin : in out T);
   --# derives TheAdmin from TheAdmin;
   --# pre  IsPresent(TheAdmin);
   --# post not IsDoingOp(TheAdmin) and
   --#      prf_rolePresent(TheAdmin) = prf_rolePresent(TheAdmin~) and
   --#      IsPresent(TheAdmin);


   ------------------------------------------------------------------
   -- SecurityOfficerIsPresent
   --
   -- Description:
   --    Returns true if a Security Officer is present
   --
   -- traceunit : C.Admin.SecurityOfficerIsPresent
   -- traceto   : FD.Interface.UpdateScreen
   ------------------------------------------------------------------

   function SecurityOfficerIsPresent (TheAdmin : T) return Boolean;


   private
      type T is
         record
            RolePresent : PrivTypes.PrivilegeT;
            CurrentOp   : OpAndNullT;
         end record;

      type AvailOpsT is array (OpT) of Boolean;
      type PrivToAvailOpsT is array (PrivTypes.AdminPrivilegeT) of AvailOpsT;

      IsAvailable : constant PrivToAvailOpsT :=
            PrivToAvailOpsT'(
                  PrivTypes.Guard           => AvailOpsT'(
                                                     OverrideLock => True,
                                                     others       => False
                                                     ),
                  PrivTypes.AuditManager    => AvailOpsT'(
                                                     ArchiveLog => True,
                                                     others     => False
                                                     ),
                  PrivTypes.SecurityOfficer => AvailOpsT'(
                                                     UpdateConfigData => True,
                                                     ShutdownOp       => True,
                                                     others           => False
                                                     )
                  );


end Admin;
