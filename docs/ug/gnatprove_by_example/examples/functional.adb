package body Functional with
  SPARK_Mode
is
   Max1 : Natural := 0;  --  max value seen
   Max2 : Natural := 0;  --  second max value seen

   function Invariant return Boolean is (Max2 <= Max1);

   function Max_Value_Seen return Integer is (Max1);

   function Second_Max_Value_Seen return Integer is (Max2);

   procedure Update (X : Natural) with
     Pre  => X > Max2 and then      --  support of maintenance
             Invariant,             --  invariant checking
     Post => Invariant and then     --  invariant checking
             (if X > Max1'Old then  --  complete functional
                Max2 = Max1'Old and Max1 = X
              elsif X < Max1'Old then
                Max2 = X and Max1 = Max1'Old
              else
                Max2 = Max2'Old and Max1 = Max1'Old)
   is
   begin
      if X > Max1 then
         Max2 := Max1;
         Max1 := X;
      elsif X < Max1 then
         Max2 := X;
      end if;
   end Update;

   procedure Seen_One (X : Integer) is
   begin
      if X > Max2 then
         Update (X);
      end if;
   end Seen_One;

   procedure Seen_Two (X, Y : Natural) is
   begin
      if X > Max1 then
         Max1 := Y;
         Max2 := X;
      elsif X > Max2 then
         Update (Y);
         Seen_One (X);
      else
         Seen_One (Y);
      end if;
   end Seen_Two;

end Functional;
