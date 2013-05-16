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
-- AdminToken.Interface
--
-- Implementation Notes:
--    Not Examined.
--
------------------------------------------------------------------

with TokenReader;

package body AdminToken.Interface
is


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    This has no function as the intialisation is done for all
   --    tokens in the user token interface.
   ------------------------------------------------------------------

   procedure Init
   is
   begin
      null;
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
       TokenReader.Poll(Reader => TokenReader.Admin);
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
      return TokenReader.TheTokenPresence(Reader => TokenReader.Admin);
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
      return TokenReader.TheTokenID(Reader => TokenReader.Admin);
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
      return TokenReader.TheTokenTry(Reader => TokenReader.Admin);
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
        ( Reader   => TokenReader.Admin,
          CertType => CertType,
          RawCert  => RawCert,
          Found    => Found);
   end GetCertificate;

end AdminToken.Interface;
