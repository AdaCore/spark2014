with Ada.Unchecked_Conversion;

package body Untangle is

   type Byte is mod 2 ** 8;

   type Word_A is record
      Lo : Byte;
      Hi : Byte;
   end record;

   type Word_B is mod 2 ** 16;

   type Word_Array is array (1 .. 10) of Word_A;

   type Thing is record
      A : Boolean;
      B : Word_Array;
      C : Boolean;
   end record;

   type Optional_Thing (Exists : Boolean := False) is record
      case Exists is
         when True =>
            T : Thing;
         when False =>
            null;
      end case;
   end record;

   G : Boolean := True;

   function Wibble (N : Natural) return Natural
   is (N)
   with Global => (Proof_In => G),
        Pre    => G;

   procedure Zero_Hi (X : in out Optional_Thing;
                      N : Natural)
   with Global => (Proof_In => G)
   is
   begin
      X.T.B (Wibble (N)).Hi := 0;
   end Zero_Hi;


end Untangle;
