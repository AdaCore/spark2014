with Interfaces; use Interfaces;
with System;

package Types is pragma SPARK_Mode (On);
   type Return_Code_T is (OK, Invalid_Query);

   type Octet is record
      Data : Unsigned_8;
   end record;
   for Octet use record
      Data at 0 range 0 .. 7;
   end record;
   for Octet'Size use 8;
   for Octet'Bit_Order use System.High_Order_First; -- REQ-3

   subtype Bit_Range is Natural range 0..7;

   type Network_DNS_Query_Range is range 0..512; -- REQ-1.1
   type Network_DNS_Query is array (Network_DNS_Query_Range) of Octet; -- REQ-1

   type Query_Opcode is (Standard_Query, Inverse_Query);
   type Qdcount_Range is range 1..16;

   type Query_Header is record
      ID : Unsigned_16;
      OPCODE : Query_Opcode;
      QDCOUNT : Qdcount_Range;
   end record;

end;
