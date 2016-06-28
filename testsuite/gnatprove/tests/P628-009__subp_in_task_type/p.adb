package body P is

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

   procedure PP (X : Integer) is

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
