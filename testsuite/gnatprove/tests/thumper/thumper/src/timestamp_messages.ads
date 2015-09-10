---------------------------------------------------------------------------
-- FILE    : timestamp_messages.adb
-- SUBJECT : Specification of a package defining timestamps.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Hermes.OID;
with Serial_Generator;

package Timestamp_Messages is

   -- Currently only version 1 is supported.
   subtype Version_Type is Positive range 1 .. 1;

   -- Currently only 256 bit hash values are supported. To lift this restriction Timestamp
   -- could be made discriminated on the hash size. However, that changes it to an indefinite
   -- type. See package Data_Storage for issues that will (currently) cause.
   --
   Hash_Size : constant := 32;

   type Timestamp is
      record
         Version : Version_Type;
         Policy  : Hermes.OID.Object_Identifier;

         -- The following two components specify the Message_Imprint sequence.
         Hash_Algorithm : Hermes.OID.Object_Identifier;  -- Currently only SHA-256.
         Hashed_Message : Hermes.Octet_Array(1 .. Hash_Size);

         Serial_Number : Serial_Generator.Serial_Number_Type;
         Generalized_Time : Hermes.Octet_Array(1 .. 14);
      end record;


   type Request is
      record
         Placeholder : Integer;
      end record;


   type Response is
      record
         Placeholder : Integer;
      end record;


end Timestamp_Messages;
