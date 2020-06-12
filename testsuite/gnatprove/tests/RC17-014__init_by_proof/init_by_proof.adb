with Ada.Text_IO;
procedure Init_By_Proof with SPARK_Mode is

   type Int_Array is array (Positive range <>) of Integer;
   pragma Annotate (GNATprove, Init_By_Proof, Int_Array);
   --  array of potentially uninitialized integers

   type Int_Array_Init is array (Positive range <>) of Integer;
   --  array of integers with normal traitment

   procedure Init_By_4 (A : out Int_Array; Error : out Boolean) with
     Pre => A'Length = 4,
     Post => (if not Error then A'Valid_Scalars)
   is
   begin
      A := (1 .. 4 => 10);
      Error := False;
   end Init_By_4;

   procedure Read (Buf   : out Int_Array;
                   Size  : Natural;
                   Error : out Boolean)
   with Pre => Buf'Length >= Size,
     Post => (if not Error then
                Buf (Buf'First .. Buf'First + (Size - 1))'Valid_Scalars)
   is
      Offset    : Natural := Size mod 4;
      Nb_Chunks : Natural := Size / 4;
   begin
      if Offset /= 0 then
         Error := True;
         return;
      else
         Error := False;
      end if;

      for Loop_Var in 0 .. Nb_Chunks - 1 loop
         pragma Loop_Invariant
           (Buf (Buf'First .. Buf'First + (Loop_Var * 4) - 1)'Valid_Scalars);
         Init_By_4 (Buf (Buf'First + Loop_Var * 4 .. Buf'First + Loop_Var * 4 + 3), Error);
         exit when Error;
      end loop;

   end Read;

   procedure Process (Buf  : in out Int_Array;
                      Size : Natural)
   with Pre => Buf'Length >= Size and then
     Buf (Buf'First .. Buf'First + (Size - 1))'Valid_Scalars,
        Post => Buf (Buf'First .. Buf'First + (Size - 1))'Valid_Scalars
   is
   begin
      for I in Buf'First .. Buf'First + (Size - 1) loop
         pragma Loop_Invariant
           (Buf (Buf'First .. Buf'First + (Size - 1))'Valid_Scalars);
         Buf (I) := Buf (I) / 2 + 5;
      end loop;
   end Process;

   procedure Process (Buf  : in out Int_Array_Init;
                      Size : Natural)
     with Pre => Buf'Length >= Size
   is
   begin
      for I in Buf'First .. Buf'First + (Size - 1) loop
         Buf (I) := Buf (I) / 2 + 5;
      end loop;
   end Process;

   Buf   : Int_Array (1 .. 150);
   Error : Boolean;
   X     : Integer;
begin
   pragma Assert (not Buf'Valid_Scalars); -- @ASSERT:FAIL
   Read (Buf, 100, Error);
   if not Error then
      X := Buf (10);
      Process (Buf, 100);
      declare
         B : Int_Array_Init := Int_Array_Init (Buf (1 .. 100));
      begin
         Process (B, 50);
      end;
      X := Buf (20);
      X := Buf (110); -- @INIT_BY_PROOF:FAIL
   end if;
end Init_By_Proof;
