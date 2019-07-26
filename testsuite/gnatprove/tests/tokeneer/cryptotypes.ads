
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
-- CryptoTypes
--
-- Description:
--...
--
------------------------------------------------------------------
with CommonTypes;

package CryptoTypes is

   -- ISSUER
   -- Identifies an entity; could be an certificate Issuer or a subject.
   subtype NameCountT is Natural range 0..40;
   subtype NameI is NameCountT range 1..40;
   subtype NameT is String(NameI);
   BlankName : constant NameT := NameT'(others => ' ');

   type IssuerIDT is range 0..2**32 - 1;

   type IssuerT is record
      ID         : IssuerIDT;
      NameLength : NameCountT;
      Name       : NameT;
   end record;

   NullIssuer : constant IssuerT :=
     IssuerT'(ID         => IssuerIDT'First,
              NameLength => NameCountT'First,
              Name       => BlankName);

   type AlgorithmT is
     (-- signing/verifying
      RSA,
      -- digesting
      MD2,
      MD5,
      SHA_1,
      RIPEMD128,
      RIPEMD160,
      -- combined mechanisms
      MD2_RSA,
      MD5_RSA,
      SHA1_RSA,
      RIPEMD128_RSA,
      RIPEMD160_RSA);


   -- KeyType
   type KeyTypeT is (PublicKey, PrivateKey);

   type KeyIDT is range 0..2**32 - 1;

   -- Support 1024 bit RSA, so acceptable key lengths (in bytes)
   -- is up to 128
   type KeyLengthT is range 0..128;

   -- KEYPART
   type KeyPartT is record
      AlgorithmID : AlgorithmT;
      KeyID       : KeyIDT;
      KeyLength   : KeyLengthT;
   end record;

   NullKeyPart : constant KeyPartT :=
     KeyPartT'(AlgorithmID => AlgorithmT'First,
               KeyID       => KeyIDT'First,
               KeyLength   => KeyLengthT'First);

end CryptoTypes;
