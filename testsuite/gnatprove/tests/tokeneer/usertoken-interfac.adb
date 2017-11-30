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
-- UserToken.Interfac
--
-- Implementation Notes:
--    Not Examined.
--
------------------------------------------------------------------

with TokenReader;

package body UserToken.Interfac
  with SPARK_Mode => Off
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
   -----------------------------------------------------------------
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
   function TheTokenPresence return CommonTypes.PresenceT is
     (TokenReader.TheTokenPresence(Reader => TokenReader.User));

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function TheTokenID return TokenTypes.TokenIDT is
     (TokenReader.TheTokenID(Reader => TokenReader.User));

   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function TheTokenTry return TokenTypes.TryT is
     (TokenReader.TheTokenTry(Reader => TokenReader.User));

   ------------------------------------------------------------------
   -- GetCertificate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure GetCertificate
     (CertType : in     CertTypes.CertificateT;
      RawCert  :    out CertTypes.RawCertificateT;
      Found    :    out Boolean)
   is
   begin
      TokenReader.GetCertificate
        (Reader   => TokenReader.User,
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
     (RawCert : in     CertTypes.RawCertificateT;
      Success :    out Boolean)
   is
   begin
      TokenReader.WriteAuthCertificate
        (RawCert => RawCert,
         Success => Success);
   end WriteAuthCertificate;

end UserToken.Interfac;
