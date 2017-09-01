package P is
   type T is private;

   package Q is
      function F return Boolean is (True);
   end;

private
   type T is record
      A : Integer;
   end record
     with Type_Invariant => Q.F;
end;
