---------------------------------------------------------------------------
-- FILE    : network-addresses.ads
-- SUBJECT : Specification of a network address handling package.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package Network.Addresses is

   type Port_Type is range 0 .. 2**16 - 1;

   type IPv4  is private;
   type UDPv4 is private;

   type Status_Type is (Success, Invalid_Address, Insufficient_Space);

   -- Convert "x.y.z.w" addresses into a suitable binary representation. Returns an Invalid
   -- Address status if the address is not in an acceptable form. All values x, y, z, and w must
   -- be between 0 and 255 in decimal. No leading, trailing or embedded non-digits allowed.
   --
   procedure To_IPv4_Address(Text : in String; Result : out IPv4; Status : out Status_Type)
     with
       Global => null,
       Depends => ( (Result, Status) => Text );

   -- Convert the binary representation of an IP address to "x.y.z.w" notation. Character_Count
   -- is the number of characters in the output string that were used.
   --
   subtype Address_String_Index_Type is Positive range 1 .. 15;
   subtype Address_String_Type is String(Address_String_Index_Type);
   subtype Address_Length_Type is Natural range 7 .. 15;

   procedure To_IPv4_String
     (Address         : in  IPv4;
      Text            : out Address_String_Type;
      Character_Count : out Address_Length_Type)
     with
       Global => null,
       Depends => ( (Text, Character_Count) => Address );

   -- Combines an IP address and port number into a UDP endpoint address.
   function To_UDPv4_Address(Address : in IPv4; Port : in Port_Type) return UDPv4;

   -- Returns the port number associated with a given UDP endpoint address.
   function Get_Port(Endpoint_Address : in UDPv4) return Port_Type;

   -- Returns the IP address associated with a given UDP endpoint address.
   function Get_IPv4(Endpoint_Address : in UDPv4) return IPv4;

private

   subtype IPv4_Address_Index_Type is Integer range 1 .. 4;
   type IPv4 is array(IPv4_Address_Index_Type) of Network.Octet;

   type UDPv4 is
      record
         Address : IPv4;
         Port    : Port_Type;
      end record;

end Network.Addresses;
