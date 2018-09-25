package body Pack with SPARK_Mode is

   function Get_Integer return Integer is
   begin
      return 123 + X;
   end Get_Integer;

   Int_Ren : Integer renames Get_Integer;

   procedure Proc1 (Result : out Integer) with Global => null;
   procedure Proc2 (Result : out Integer) with Global => null;
   procedure Proc3 (Result : out Integer) with Global => null;

   procedure Proc1 (Result : out Integer) is
   begin
      Result := Int_Ren;
   end;

   procedure Proc2 (Result : out Integer) is
   begin
      Result := X;
   end;

   procedure Proc3 (Result : out Integer) is
   begin
      Result := Get_Integer;
   end;

end Pack;
