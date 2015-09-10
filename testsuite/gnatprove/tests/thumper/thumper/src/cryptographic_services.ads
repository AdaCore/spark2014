---------------------------------------------------------------------------
-- FILE    : cryptographic_services.ads
-- SUBJECT : Specification of a package to abstract the crypto needed by Thumper.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Hermes;

package Cryptographic_Services
with
  Abstract_State => (Key, Hash)
is
   type Status_Type is (Success, Bad_Key);

   -- Reads the server's private key from file system.
   --
   procedure Initialize_Key(Status : out Status_Type)
     with
       Global => (Output => Key),
       Depends => ((Key, Status) => null);


   -- Computes the signature of Data using a constant private key that is internal to this
   -- package, returning the result.
   --
   function Make_Signature(Data : in  Hermes.Octet_Array) return Hermes.Octet_Array
     with Global => (Input => Key);


   -- Prepares the internal hash for use.
   --
   procedure Initialize_Hash
     with
       Global => (Output => Hash),
       Depends => (Hash => null);


   -- Updates the hash using the given data. This procedure can be called repeatedly to hash
   -- a large amount of data. The size of the Data array can be anything (even zero) and need
   -- not be the same size between calls.
   --
   procedure Update_Hash(Data : in Hermes.Octet_Array)
     with
       Global => (In_Out => Hash),
       Depends => (Hash =>+ Data);


   -- Finalizes the hash computation and returns the result.
   --
   function Finalize_Hash return Hermes.Octet_Array
     with Global => (Input => Hash);


end Cryptographic_Services;
