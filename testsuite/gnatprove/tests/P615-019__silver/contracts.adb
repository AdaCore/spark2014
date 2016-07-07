procedure Contracts is

   procedure Convert_Integer0 (X : Integer; U : out Natural) is
   begin
      U := X;
   end Convert_Integer0;

   procedure Convert_Integer (X : Integer; U : out Natural)
     with Pre => X >= 0
   is
   begin
      U := X;
   end Convert_Integer;

   procedure Convert_Integer1 (X : Integer; U : out Natural)
     with Pre  => X >= 0,
          Post => X = U
   is
   begin
      U := X;
   end Convert_Integer1;

   procedure Call_Convert_Integer (Y : in out Natural) is
      Z : Natural;
   begin
      Convert_Integer (Y, Z);
      Y := Y - Z;
   end Call_Convert_Integer;

   procedure Call_Convert_Integer1 (Y : in out Natural) is
      Z : Natural;
   begin
      Convert_Integer1 (Y, Z);
      Y := Y - Z;
   end Call_Convert_Integer1;

begin
   null;
end Contracts;
