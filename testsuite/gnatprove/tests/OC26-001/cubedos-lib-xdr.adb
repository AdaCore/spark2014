--------------------------------------------------------------------------------
-- FILE   : cubedos-lib-xdr.ads
-- SUBJECT: Body of an XDR encoding/decoding package.
-- AUTHOR : (C) Copyright 2015 by Vermont Technical College
--
--------------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Ada.Unchecked_Conversion;

package body CubedOS.Lib.XDR is

   function XDR_Integer_To_Unsigned is
     new Ada.Unchecked_Conversion(Source => XDR_Integer, Target => XDR_Unsigned);
   function XDR_Unsigned_To_Integer is
     new Ada.Unchecked_Conversion(Source => XDR_Unsigned, Target => XDR_Integer);

   function XDR_Hyper_To_Unsigned is
     new Ada.Unchecked_Conversion(Source => XDR_Hyper, Target => XDR_Unsigned_Hyper);
   function XDR_Unsigned_To_Hyper is
     new Ada.Unchecked_Conversion(Source => XDR_Unsigned_Hyper, Target => XDR_Hyper);


   procedure Encode
     (Value    : in     XDR_Integer;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
   is
   begin
      Encode(XDR_Integer_To_Unsigned(Value), Data, Position, Last);
   end Encode;


   procedure Encode
     (Value    : in     XDR_Unsigned;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
   is
      Temporary_1 : XDR_Unsigned := Value;
      Temporary_2 : XDR_Unsigned;
   begin
      for I in 1 .. 4 loop
         Temporary_2 := Temporary_1 rem 256;
         Data(Position + (4 - I)) := Octet(Temporary_2);
         Temporary_1 := Temporary_1 / 256;
      end loop;
      Last := Position + (4 - 1);
   end Encode;


   procedure Encode
     (Value    : in     XDR_Boolean;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
   is
      Temporary : XDR_Unsigned;
   begin
      if Value = XDR_False then
         Temporary := 0;
      else
         Temporary := 1;
      end if;
      Encode(Temporary, Data, Position, Last);
   end Encode;


   procedure Encode
     (Value    : in     XDR_Hyper;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
   is
   begin
      Encode(XDR_Hyper_To_Unsigned(Value), Data, Position, Last);
   end Encode;


   procedure Encode
     (Value    : in     XDR_Unsigned_Hyper;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
   is
      Temporary_1 : XDR_Unsigned_Hyper := Value;
      Temporary_2 : XDR_Unsigned_Hyper;
   begin
      for I in 1 .. 8 loop
         Temporary_2 := Temporary_1 rem 256;
         Data(Position + (8 - I)) := Octet(Temporary_2);
         Temporary_1 := Temporary_1 / 256;
      end loop;
      Last := Position + (8 - 1);
   end Encode;


   procedure Encode
     (Value    : in     Octet_Array;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Extended_Index)
   is
      Padding_Start : Octet_Array_Index;
      Padding_Stop : Octet_Array_Index;
   begin
      Data(Position .. (Position + Value'Length - 1)) := Value;

      -- Add padding if necessary.
      if Value'Length rem 4 /= 0 then
         Padding_Start := Position + Value'Length;
         Padding_Stop := Padding_Start + (3 - Value'Length rem 4);
         Data(Padding_Start .. Padding_Stop) := (others => 0);
      end if;
      Last := Position + (Length_With_Padding(Value'Length) - 1);
   end Encode;


   procedure Encode
     (Value    : in     String;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Extended_Index)
   is
      Temporary_Array : Octet_Array(0 .. Value'Length - 1);
   begin
      Temporary_Array := (others => 0);
      for I in Value'Range loop
         Temporary_Array(I - Value'First) := Character'Pos(Value(I));
      end loop;
      Encode(Temporary_Array, Data, Position, Last);
   end Encode;


   ----------------------
   -- Decoding Procedures
   ----------------------

   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Integer;
      Last     : out Octet_Array_Index)
   is
      Temp : XDR_Unsigned;
   begin
      Decode(Data, Position, Temp, Last);
      Value := XDR_Unsigned_To_Integer(Temp);
   end Decode;


   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Unsigned;
      Last     : out Octet_Array_Index)
   is
      Temporary_1 : XDR_Unsigned := XDR_Unsigned(Data(Position));
      Temporary_2 : XDR_Unsigned;
   begin
      for I in 1 .. 3 loop
         Temporary_2 := Temporary_1 * 256;
         Temporary_2 := Temporary_2 + XDR_Unsigned(Data(Position + I));
         Value := Temporary_2;
         Temporary_1 := Value;
      end loop;
      Last := Position + 3;
   end Decode;


   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Boolean;
      Last     : out Octet_Array_Index)
   is
      Temporary : XDR_Unsigned;
   begin
      Decode(Data, Position, Temporary, Last);
      -- TODO: Any non-zero value is taken to be True. Is that what we really want?
      if Temporary /= 0 then
         Value := XDR_True;
      else
         Value := XDR_False;
      end if;
   end Decode;


   -- TODO: Account for negatives.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Hyper;
      Last     : out Octet_Array_Index)
   is
      Temporary : XDR_Unsigned_Hyper;
   begin
      Decode(Data, Position, Temporary, Last);
      Value := XDR_Unsigned_To_Hyper(Temporary);
   end Decode;


   -- Decodes an unsigned hyper integer from Data starting at Position up to and including Last.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Unsigned_Hyper;
      Last     : out Octet_Array_Index)
   is
      Temporary_1 : XDR_Unsigned_Hyper := XDR_Unsigned_Hyper(Data(Position));
      Temporary_2 : XDR_Unsigned_Hyper;
   begin
      for I in 1 .. 7 loop
         Temporary_2 := Temporary_1 * 256;
         Temporary_2 := Temporary_2 + XDR_Unsigned_Hyper(Data(Position + I));
         Value := Temporary_2;
         Temporary_1 := Value;
      end loop;
      Last := Natural(Position + 7);
   end Decode;


   -- Decodes a fixed length array of opaque data from Data starting at Position.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out Octet_Array;
      Last     : out Octet_Array_Extended_Index)
   is
   begin
      Value := Data(Position .. Position + Value'Length - 1);
      Last := Position + (Length_With_Padding(Value'Length) - 1);
   end Decode;


   -- Decodes a fixed length string from Data starting at Position.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out String;
      Last     : out Octet_Array_Extended_Index)
   is
   begin
      Value := (others => ' ');
      for I in Position .. (Position + Value'Length - 1) loop
         Value(Value'First + (I - Position)) := Character'Val(Data(I));
      end loop;
      Last := Position + (Length_With_Padding(Value'Length) - 1);
   end Decode;


end CubedOS.Lib.XDR;
