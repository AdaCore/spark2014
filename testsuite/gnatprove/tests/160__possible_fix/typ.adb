with Interfaces; use Interfaces;

procedure Typ (U : Unsigned_32; S : Integer_32) with
  SPARK_Mode,
  Global => null
is

   X16 : Integer_16;
   subtype Int16 is Integer_16 range 42 .. Integer_16'Last;
   Y16 : Int16;

   X32 : Integer_32;
   subtype Int32 is Integer_32 range 42 .. Integer_32'Last;
   Y32 : Int32;

   X64 : Integer_64;
   subtype Int64 is Integer_64 range 42 .. Integer_64'Last;
   Y64 : Int64;

   U16 : Unsigned_16;
   U32 : Unsigned_32;
   U64 : Unsigned_64;

   function Rand (X : Integer) return Boolean with Import, Global => null;

begin
   if Rand (0) then
      X16 := Integer_16 (U);
   elsif Rand (1) then
      Y16 := Int16 (U);
   elsif Rand (2) then
      X32 := Integer_32 (U);
   elsif Rand (3) then
      Y32 := Int32 (U);
   elsif Rand (4) then
      X64 := Integer_64 (U);
   elsif Rand (5) then
      Y64 := Int64 (U);

   elsif Rand (6) then
      X16 := Integer_16 (S);
   elsif Rand (7) then
      Y16 := Int16 (S);
   elsif Rand (8) then
      X32 := Integer_32 (S);
   elsif Rand (9) then
      Y32 := Int32 (S);
   elsif Rand (10) then
      X64 := Integer_64 (S);
   elsif Rand (11) then
      Y64 := Int64 (S);

   elsif Rand (12) then
      U16 := Unsigned_16 (U);
   elsif Rand (13) then
      U32 := Unsigned_32 (U);
   elsif Rand (14) then
      U64 := Unsigned_64 (U);

   elsif Rand (15) then
      U16 := Unsigned_16 (S);
   elsif Rand (16) then
      U32 := Unsigned_32 (S);
   elsif Rand (17) then
      U64 := Unsigned_64 (S);
   end if;
end;
