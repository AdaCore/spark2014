package body Unconstr_Call is

   procedure P (X : T) is
      Z : Integer;
   begin
      if X'Length > 0 then
         Z := X (X'First);
      else
         Z := 0;
      end if;
   end P;

   procedure Havoc (X : in out T) is
      Tmp : Integer;
   begin
      if X'Length > 1 then
         Tmp := X (X'First);
         X (X'First) := X (X'Last);
         X (X'Last) := Tmp;
      end if;
   end Havoc;

   procedure Test_1 (Z : in out T) is
   begin
      P (Z);
   end Test_1;

   procedure Test_2 (Z : in out T) is
      X : constant Integer := Z'First;
   begin
      Havoc (Z);
      pragma Assert (X = Z'First);
   end Test_2;

end Unconstr_Call;
