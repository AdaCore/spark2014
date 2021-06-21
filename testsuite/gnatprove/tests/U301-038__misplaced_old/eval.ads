pragma Unevaluated_Use_Of_Old (Allow);
package Eval is
   type Value is new Integer;
   type My_Array is array (Integer range <>) of Value;

   procedure Extract (A : My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = A(J)'Old);
end Eval;
