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
-- AdminToken
--
-- Description:
--    ...
--
------------------------------------------------------------------

with AuditTypes;
with PrivTypes;
--# inherit
--#    AuditTypes,
--#    BasicTypes,
--#    CertTypes,
--#    Cert.Attr.Auth,
--#    Cert.ID,
--#    CertificateStore,
--#    Clock,
--#    ConfigData,
--#    CryptoTypes,
--#    AuditLog,
--#    KeyStore,
--#    PrivTypes,
--#    TokenTypes;

package AdminToken
--# own State : StateType;
--#     Status,
--#     in Input;
--# initializes Status;
is


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   --# type StateType is abstract;
   --# function TheAuthCertRole(TheState : StateType) return
   --#               PrivTypes.PrivilegeT;
   --# function prf_isGood(TheState : StateType) return Boolean;
   --# function prf_authCertValid(TheState : StateType) return Boolean;
   --#

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the admin token reader.
   --
   -- Traceunit: C.AdminToken.Init
   -- Traceto:  FD.TIS.TISStartup
   ------------------------------------------------------------------

   procedure Init ;
   --# global in out Status;
   --#           out State;
   --# derives Status,
   --#         State  from Status;
   --# post not prf_isGood(State) and
   --#      not prf_authCertValid(State) and
   --#      not ( TheAuthCertRole(State)
   --#               in PrivTypes.AdminPrivilegeT );


   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the external reader, and also the token if present, and
   --    updates State accordingly. A Card is only considered present
   --    once communications have been initiated, and the token ID has been
   --    extracted.
   --    May log a system fault.
   --
   -- Traceunit: C.AdminToken.Poll
   -- traceto : FD.Interface.TISPoll
   ------------------------------------------------------------------
   procedure Poll;
   --# global in     Input;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out Status;
   --#        in out State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives Status             from * &
   --#         State              from *,
   --#                                 Status,
   --#                                 Input &
   --#         AuditLog.State,
   --#         AuditLog.FileState from *,
   --#                                 Status,
   --#                                 State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now;
   --# post ( prf_isGood(State~) <->
   --#           prf_isGood(State) ) and
   --#      ( prf_authCertValid(State~) <->
   --#           prf_authCertValid(State) ) and
   --#      ( TheAuthCertRole(State~) = PrivTypes.Guard <->
   --#           TheAuthCertRole(State) = PrivTypes.Guard );


   ------------------------------------------------------------------
   -- ReadandCheck
   --
   -- Description:
   --    Reads certificates from the token.
   --    May log a system fault.
   --
   -- Traceunit: C.AdminToken.ReadAndCheck
   -- Traceto : FD.AdminToken.AdminTokenOK
   -- Traceto : FD.AdminToken.AdminTokenNotOK
   ------------------------------------------------------------------
   procedure ReadAndCheck
     (Description :    out AuditTypes.DescriptionT;
      TokenOK     :    out Boolean);
   --# global in     Input;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.State;
   --#        in     KeyStore.Store;
   --#        in out Status;
   --#        in out State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives State,
   --#         TokenOK,
   --#         Description        from Status,
   --#                                 State,
   --#                                 Input,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.State,
   --#                                 KeyStore.Store &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Status,
   --#                                 State,
   --#                                 Input,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 KeyStore.Store &
   --#         Status             from *,
   --#                                 State;
   --# post ( TokenOk <-> ( prf_isGood(State) and
   --#                      prf_authCertValid(State) and
   --#                      TheAuthCertRole(State)
   --#                        in PrivTypes.AdminPrivilegeT ) );


   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Description:
   --    Returns True extactly when the token is present
   --
   -- Traceunit : C.AdminToken.IsPresent
   -- Traceto :  FD.RealWorld.State
   ------------------------------------------------------------------
   function IsPresent return Boolean;
   --# global State;

   ------------------------------------------------------------------
   -- IsCurrent
   --
   -- Description:
   --    Returns True extactly when the auth cert on the token is current
   --
   -- Traceunit : C.AdminToken.IsCurrent
   -- Traceto :  FD.AdminToken.Current
   ------------------------------------------------------------------
   function IsCurrent return Boolean;
   --# global State,
   --#        Clock.CurrentTime;


   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Description:
   --    Returns the user associated with the current token.
   --
   -- Traceunit : C.AdminToken.ExtractUser
   -- Traceto :  FD.AuditLog.ExtractUser
   ------------------------------------------------------------------
   function ExtractUser return AuditTypes.UserTextT;
   --# global State;


   ------------------------------------------------------------------
   -- GetRole
   --
   -- Description:
   --    obtains the role value for the Auth certificate.
   --
   -- Traceunit : C.AdminToken.GetRole
   -- Traceto :  FD.AdminToken.AdminTokenOK
   -- Traceto :  FD.Enclave.ValidateAdminTokenOK
   ------------------------------------------------------------------
   function GetRole return PrivTypes.AdminPrivilegeT;
   --# global State;
   --# pre prf_isGood(State) and
   --#     prf_authCertValid(State) and
   --#     TheAuthCertRole(State)
   --#        in PrivTypes.AdminPrivilegeT;



   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears UserToken.State certificate information
   --
   -- Traceunit: C.AdminToken.Clear
   -- Traceto : FD.AdminToken.Clear
   ------------------------------------------------------------------
   procedure Clear;
   --# global in out State;
   --# derives State from *;
   --# post not prf_isGood(State) and
   --#      not prf_authCertValid(State) and
   --#      not ( TheAuthCertRole(State)
   --#               in PrivTypes.AdminPrivilegeT );


end AdminToken;
