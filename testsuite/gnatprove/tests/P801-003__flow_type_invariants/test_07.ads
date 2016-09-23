with Util; use Util;

package Test_07 with Elaborate_Body is

   type T is private;

private

   type T is record
      A : Boolean := False;
      B : Boolean := True;
   end record
   with Type_Invariant => Exclusive_Or (T.A, T.B);

   --  Should be OK

end Test_07;
