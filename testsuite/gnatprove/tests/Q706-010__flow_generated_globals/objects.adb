package body Objects is
   X : Integer := 0;
   overriding procedure Proc (V : U) is
   begin
      X := X + 1;
   end Proc;
end Objects;
