with Unit; use Unit;

procedure Precond is

   function Valid (X : Integer) return Boolean;

   function Valid (X : Integer) return Boolean is
      pragma SPARK_Mode (Off);
   begin
      return True;
   end;

   function Blob (X : Integer) return Boolean is (True) with
     Pre => Valid (X);

   procedure P (X : Integer) with Pre => Valid (X) and Blob (X) is begin
      null;
   end;

   X : Integer := 42;
begin
   if Valid (X) then
      P (X);
   end if;

   pragma Assert (Bla);
end;
