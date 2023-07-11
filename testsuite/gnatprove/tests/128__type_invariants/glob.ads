with Variable; with Hidden;

package Glob is
   type T is private;

   function F return Boolean;
private
   type T is record
      B : Integer;
   end record
     with Type_Invariant => True or else F;

   Y : constant T := (B => Variable.Input);

   function F return Boolean is (Y.B = 0 and then Hidden.Proxy = 0);
end;
