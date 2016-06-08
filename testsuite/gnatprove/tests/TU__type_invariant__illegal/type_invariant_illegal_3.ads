--  TU: 2. A Type_Invariant expression shall not have a variable input.

package Type_Invariant_Illegal_3 is

   type T1 is private;
   type T2 is tagged private;

private

   B : Boolean;
   function Get return Boolean is (B);

   type T1 is null record with Type_Invariant => B;
   type T2 is tagged null record with Type_Invariant => Get;

end Type_Invariant_Illegal_3;
