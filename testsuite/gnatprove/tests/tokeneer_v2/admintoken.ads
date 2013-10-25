------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- AdminToken
--
-- Description:
--...
--
------------------------------------------------------------------

with AuditLog;
with AuditTypes;
with Clock;
with ConfigData;
with KeyStore;
with PrivTypes;
use PrivTypes;

package AdminToken
  with SPARK_Mode,
       Abstract_State => (State,
                          Status,
                          (Input with External => Async_Writers)),
       Initializes    => Status
is


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   function TheAuthCertRole return PrivTypes.PrivilegeT
     with Global => State;

   function IsGood return Boolean
     with Global => State;

   function AuthCertValid return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the admin token reader.
   --
   -- Traceunit: C.AdminToken.Init
   -- Traceto:  FD.TIS.TISStartup
   ------------------------------------------------------------------

   procedure Init
     with Global  => (Output => State,
                      In_Out => Status),
          Depends => ((State,
                       Status) => Status),
          Post    => (not IsGood) and then
                     (not AuthCertValid) and then
                     not (TheAuthCertRole in PrivTypes.AdminPrivilegeT);

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the external reader, and also the token if present, and
   --    updates State accordingly.A Card is only considered present
   --    once communications have been initiated, and the token ID has been
   --    extracted.
   --    May log a system fault.
   --
   -- Traceunit: C.AdminToken.Poll
   -- traceto : FD.Interfac.TISPoll
   ------------------------------------------------------------------
   procedure Poll
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State) => (AuditLog.FileState,
                                           AuditLog.State,
                                           Clock.Now,
                                           ConfigData.State,
                                           State,
                                           Status),
                      State =>+ (Input,
                                 Status),
                      Status =>+ null),
          Post    => (IsGood'Old = IsGood) and then
                     (AuthCertValid'Old = AuthCertValid) and then
                     ((TheAuthCertRole'Old = PrivTypes.Guard) =
                        (TheAuthCertRole = PrivTypes.Guard));

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
      TokenOK     :    out Boolean)
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 Input,
                                 KeyStore.State,
                                 KeyStore.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State) => (AuditLog.FileState,
                                           AuditLog.State,
                                           Clock.Now,
                                           ConfigData.State,
                                           Input,
                                           KeyStore.Store,
                                           State,
                                           Status),
                      (Description,
                       State,
                       TokenOK) => (Clock.CurrentTime,
                                    Input,
                                    KeyStore.State,
                                    KeyStore.Store,
                                    State,
                                    Status),
                      Status =>+ State),
          Post    => TokenOk = (IsGood and then
                                AuthCertValid and then
                                TheAuthCertRole in PrivTypes.AdminPrivilegeT);

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Description:
   --    Returns True extactly when the token is present
   --
   -- Traceunit : C.AdminToken.IsPresent
   -- Traceto :  FD.RealWorld.State
   ------------------------------------------------------------------
   function IsPresent return Boolean
     with Global  => State;

   ------------------------------------------------------------------
   -- IsCurrent
   --
   -- Description:
   --    Returns True extactly when the auth cert on the token is current
   --
   -- Traceunit : C.AdminToken.IsCurrent
   -- Traceto :  FD.AdminToken.Current
   ------------------------------------------------------------------
   function IsCurrent return Boolean
     with Global  => (Clock.CurrentTime, State);

   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Description:
   --    Returns the user associated with the current token.
   --
   -- Traceunit : C.AdminToken.ExtractUser
   -- Traceto :  FD.AuditLog.ExtractUser
   ------------------------------------------------------------------
   function ExtractUser return AuditTypes.UserTextT
     with Global  => State;

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
   function GetRole return PrivTypes.AdminPrivilegeT
     with Global  => State,
          Pre     => IsGood and then
                     AuthCertValid and then
                     TheAuthCertRole in PrivTypes.AdminPrivilegeT;

   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears UserToken.State certificate information
   --
   -- Traceunit: C.AdminToken.Clear
   -- Traceto : FD.AdminToken.Clear
   ------------------------------------------------------------------
   procedure Clear
     with Global  => (In_Out => State),
          Depends => (State =>+ null),
          Post    => (not IsGood) and then
                     (not AuthCertValid) and then
                     (not (TheAuthCertRole in PrivTypes.AdminPrivilegeT));

end AdminToken;
