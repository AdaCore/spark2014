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
-- UserToken.Interface
--
-- Implementation Notes:
--    Not Examined.
--
------------------------------------------------------------------

with TokenReader;

package body UserToken.Interface
is


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   procedure Init
   is
   begin
      TokenReader.Init;
   end Init;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   procedure Poll
   is
   begin
       TokenReader.Poll(Reader => TokenReader.User);
   end Poll;

   ------------------------------------------------------------------
   -- TheTokenPresence
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   function TheTokenPresence return BasicTypes.PresenceT
   is
   begin
      return TokenReader.TheTokenPresence(Reader => TokenReader.User);
   end TheTokenPresence;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   function TheTokenID return TokenTypes.TokenIDT
   is
   begin
      return TokenReader.TheTokenID(Reader => TokenReader.User);
   end TheTokenID;


   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   function TheTokenTry return  TokenTypes.TryT
   is
   begin
      return TokenReader.TheTokenTry(Reader => TokenReader.User);
   end TheTokenTry;

   ------------------------------------------------------------------
   -- GetCertificate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   procedure GetCertificate
     (CertType  : in     CertTypes.CertificateT;
      RawCert   :    out CertTypes.RawCertificateT;
      Found     :    out Boolean)
   is
   begin
      TokenReader.GetCertificate
        ( Reader   => TokenReader.User,
          CertType => CertType,
          RawCert  => RawCert,
          Found    => Found);
   end GetCertificate;

   ------------------------------------------------------------------
   -- WriteAuthCertificate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   procedure WriteAuthCertificate
     (RawCert   : in     CertTypes.RawCertificateT;
      Success   :    out Boolean)
   is
   begin
      TokenReader.WriteAuthCertificate
        (RawCert => RawCert,
         Success => Success);
   end WriteAuthCertificate;


end UserToken.Interface;
