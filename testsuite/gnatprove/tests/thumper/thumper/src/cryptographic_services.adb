---------------------------------------------------------------------------
-- FILE    : cryptographic_services.adb
-- SUBJECT : Body of a package to abstract the crypto needed by Thumper.
-- AUTHORS  : (C) Copyright 2015 by Peter Chapin, Nicole Hurley, and Nathan Brown
--
-- The implementation of this package is not SPARK.
--
-- Ultimately this package should be implemented by calling into an appropriate cryptographic
-- library such as OpenSSL.
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(Off);
with Interfaces.C;

package body Cryptographic_Services is


   type SHA_LONG is new Interfaces.C.unsigned;
   type SHA256_CTX_Array is array(SHA_LONG range <>) of Natural;

   -- Type definition for the structure used to create the hash.
   type SHA256_CTX is
      record
         H : SHA256_CTX_Array (1..8);
         Nl : SHA_LONG;
         Nh : SHA_LONG;
         Data : SHA256_CTX_Array (1..16);
         Num : Interfaces.C.unsigned;
         Md_Len : Interfaces.C.unsigned;
      end record
     with Convention => C;

   -- Imported hash initialization function.
   procedure SHA256_Init(Context : out SHA256_CTX)
     with
       Import,
       Convention => C,
       External_Name => "SHA256_Init";

   -- Imported hash updating function.
   procedure SHA256_Update
     (Context : in out SHA256_CTX; Data : Hermes.Octet_Array; Len : Interfaces.C.size_t)
     with
       Import,
       Convention => C,
       External_Name => "SHA256_Update";

   -- Imported hash finalization function.
   procedure SHA256_Final(Md : out Hermes.Octet_Array; Context : SHA256_CTX)
     with
       Import,
       Convention => C,
       External_Name => "SHA256_Final";


   Context : SHA256_CTX; -- Only one hash can be active at a time. This stores its context.

   procedure Initialize_Key(Status : out Status_Type) is
   begin
      -- TODO: Read the key from the file system.
      -- This procedure does not raise an exception so the main program can make progress.
      Status  := Success;
   end Initialize_Key;


   function Make_Signature(Data : in  Hermes.Octet_Array) return Hermes.Octet_Array is
      Signature : Hermes.Octet_Array(1 .. 20) := (others => 0);
   begin
      raise Program_Error with "Cryptographic_Services.Make_Signature not implemented";
      return Signature;
   end Make_Signature;


   -- Uses the imported C function SHA256_Init() to initialize the hashing procedure.
   procedure Initialize_Hash is
   begin
      SHA256_Init(Context);
   end Initialize_Hash;


   -- Uses the imported C function SHA256_Update() to continue the hashing procedure.
   procedure Update_Hash(Data : in Hermes.Octet_Array) is
   begin
      SHA256_Update(Context, Data, Interfaces.C.size_t(Data'Length));
   end Update_Hash;


   -- Uses the imported C function SHA256_Final() to finalize the hashing procedure.
   function Finalize_Hash return Hermes.Octet_Array is
      -- TODO: Replace 32 with a named number. See also Timestamp_Messages.Hash_Size.
      Final_Hash : Hermes.Octet_Array(1 .. 32) := (others => 0);
   begin
      SHA256_Final(Final_Hash, Context);
      return Final_Hash;
   end Finalize_Hash;


end Cryptographic_Services;
