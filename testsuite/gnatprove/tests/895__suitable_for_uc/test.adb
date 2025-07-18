with Ada.Unchecked_Conversion;

procedure Test with SPARK_Mode is

   --  Test overlay with unknown Esize

   function Id (X : Integer) return Integer is (X);
   type Nat_Array is array (Positive range 1 .. Id (1)) of Integer;

   procedure P (X : in out Nat_Array; Y : in out Integer) is
      XX : Integer with Import, Address => X'Address;
      YY : Nat_Array with Import, Address => Y'Address;
   begin
      null;
   end P;

   --  Test UC with unknown RM size

   function To_Nat_Array is new Ada.Unchecked_Conversion (Integer, Nat_Array);
   function From_Nat_Array is new Ada.Unchecked_Conversion (Nat_Array, Integer);

   --  Test composite with unknown size of components. It can only occur with
   --  discriminants.

   type R (D : Boolean := True) is record
      case D is
      when True => F, G, H : Character;
      when others => null;
      end case;
   end record with Size => 32;

   function To_Int is new Ada.Unchecked_Conversion (R, Integer);

   type A is array (Positive range 1 .. 3) of R;
   type H is record
      T, U, V : R;
   end record;

   function A_To_H is new Ada.Unchecked_Conversion (A, H);
   function H_To_A is new Ada.Unchecked_Conversion (H, A);
begin
   null;
end Test;
