with Ada.Unchecked_Conversion;

procedure Potentially_Invalid_Reads with spark_mode is

   type Int_8 is range -128 .. 127 with Size => 8;
   subtype Nat_8 is Int_8 range 0 .. 127;

   type My_Record is record
      F, G, H, I : Nat_8;
   end record;

   type My_Array is array (1 .. 4) of Nat_8;

   type Uint_32 is mod 2 ** 32;

   function Unsafe_Read_Record is new Ada.Unchecked_Conversion (Uint_32, My_Record) with
     Potentially_Invalid;

   function Unsafe_Read_Array is new Ada.Unchecked_Conversion (Uint_32, My_Array) with
     Potentially_Invalid;

   type Array_Or_Record (B : Boolean) is record
      case B is
         when True =>
            F_Rec : My_Record;
         when False =>
            F_Arr : My_Array;
      end case;
   end record;

   subtype Wrapped_Record is Array_Or_Record (True);
   subtype Wrapped_Array is Array_Or_Record (False);

   procedure Unsafe_Read_Record (X : out Wrapped_Record; From : Uint_32) with
     Potentially_Invalid => X,
     Global => null
   is
   begin
       X.F_Rec := Unsafe_Read_Record (From);
   end Unsafe_Read_Record;

   procedure Unsafe_Read_Array (X : out Wrapped_Array; From : Uint_32) with
     Potentially_Invalid => X,
     Global => null
   is
   begin
       X.F_Arr := Unsafe_Read_Array (From);
   end Unsafe_Read_Array;

   procedure Unsafe_Read (X : out Array_Or_Record; From : Uint_32) with
     Potentially_Invalid => X,
     Global => null
   --  Read a potential invalid value of an array or record from From

   is
   begin
      if X.B then
         Unsafe_Read_Record (X, From);
      else
         Unsafe_Read_Array (X, From);
      end if;
   end Unsafe_Read;

   Read_Error : exception;

   procedure Safe_Read (X : out Array_Or_Record; From : Uint_32) with
     Potentially_Invalid => X,
     Exceptional_Cases => (Read_Error => True),
     Post => X'Valid_Scalars,
     Global => null
   --  Read the value of an array or record from From and raise an exception if
   --  it is invalid.

   is
   begin
      Unsafe_Read (X, From);
      if not X'Valid_Scalars then
         raise Read_Error;
      end if;
   end Safe_Read;

   procedure Treat_Array_Or_Record (X : in out Array_Or_Record) with
     Import,
     Global => null,
     Always_Terminates;
   --  Do some treatment on a valid array or record

   procedure Use_Safe_Read (X : out Array_Or_Record; From : Uint_32) with
     Exceptional_Cases => (Read_Error => True),
     Global => null
   -- Use Safe_Read to read a valid value

   is
   begin
      Safe_Read (X, From);
      Treat_Array_Or_Record (X);
   end Use_Safe_Read;

   procedure Use_Unsafe_Read (X : out Array_Or_Record; From : Uint_32) with
     Global => null
   -- Use Unsafe_Read, a validity check is emitted by the tool

   is
   begin
      Unsafe_Read (X, From);
      Treat_Array_Or_Record (X);
   end Use_Unsafe_Read;

begin
  null;
end;
