package body P is

   task type TT (X : Integer);

   task body TT is

      Y : Integer;

      procedure Proc with Pre => True;

      procedure Proc is
      begin
         Y := X;
      end;

   begin
      Proc;
   end;

end;
