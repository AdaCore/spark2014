procedure Enum is
   type My_Enum is (A, B, C);

   X : constant My_Enum := A with Warnings => Off;
   Y : constant My_Enum := A;

   procedure Dummy with Import, Global => null, Annotate => (GNATprove, Always_Return);

begin
   if X = A then
      Dummy;
   else
      Dummy;
   end if;

   if Y = A then
      Dummy;
   else
      Dummy;
   end if;
end Enum;
