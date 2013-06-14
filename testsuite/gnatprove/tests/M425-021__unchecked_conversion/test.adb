with Ada.Unchecked_Conversion;

package body Test
is

   type Record_A is record
      A : Boolean;
      B : Boolean;
      C : Boolean;
   end record;

   type Record_A2 is record
      X, Y, Z : Boolean;
   end record;

   function To_A2 is new Ada.Unchecked_Conversion (Source => Record_A,
                                                   Target => Record_A2);

   type Array_T is array (Natural) of Record_A;

   type Record_B is record
      A : Array_T;
      B : Integer;
      C : Boolean;
      D : Record_A;
   end record;

   procedure Op_R5 (X : in out Record_A;
                    Y : Record_A2)
   is
   begin
      X.A := Y.Y;
   end Op_R5;

   procedure UCC_01 (A : in out Record_A)
   is
   begin
      Op_R5 (A, To_A2 (A));  -- illegal
   end UCC_01;

end Test;
