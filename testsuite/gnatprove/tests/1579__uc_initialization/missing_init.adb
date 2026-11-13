with Ada.Unchecked_Conversion;
with Interfaces;

procedure Missing_Init (Value : out Interfaces.Unsigned_32)
  with SPARK_Mode
is
   type Relaxed_Part is record
      Value : Interfaces.Unsigned_32;
   end record with Relaxed_Initialization, Size => 32;
   for Relaxed_Part use record
      Value at 0 range 0 .. 31;
   end record;

   type Words is array (1 .. 4) of Interfaces.Unsigned_32
     with Component_Size => 32;

   --  The ordinary part avoids a wrapper for the complete source. The size
   --  above 128 bits avoids precise UC handling, isolating the missing check
   --  from the separate support for wrappers in the UC model.

   type Source is record
      Ordinary : Words;
      Relaxed  : Relaxed_Part;
   end record with Size => 160, Alignment => 4;
   for Source use record
      Ordinary at 0 range 0 .. 127;
      Relaxed at 16 range 0 .. 31;
   end record;
   type Target is array (1 .. 5) of Interfaces.Unsigned_32
     with Component_Size => 32, Alignment => 4;
   function Convert is new Ada.Unchecked_Conversion (Source, Target);

   X : Source;
begin
   X.Ordinary := (others => 0);
   declare
      Y : constant Target := Convert (X); -- @INIT_BY_PROOF:FAIL
   begin
      Value := Y (5);
   end;
end Missing_Init;
