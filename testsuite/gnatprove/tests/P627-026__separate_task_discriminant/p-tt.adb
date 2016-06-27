separate (P)
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
