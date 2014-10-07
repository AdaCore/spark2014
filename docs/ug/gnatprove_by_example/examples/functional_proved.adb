package body Functional_Proved with
  SPARK_Mode
is
   Max : Natural := 0;  --  max value seen
   Snd : Natural := 0;  --  second max value seen

   function Invariant return Boolean is
     (if Max = 0 then Snd = 0 else Snd < Max);

   function Max_Value_Seen return Integer is (Max);

   function Second_Max_Value_Seen return Integer is (Snd);

   procedure Update (X : Natural) with
     Pre  => X > Snd and then      --  support of maintenance
             Invariant,            --  invariant checking
     Post => Invariant and then    --  invariant checking
             (if X > Max'Old then  --  complete functional
                Snd = Max'Old and Max = X
              elsif X < Max'Old then
                Snd = X and Max = Max'Old
              else
                Snd = Snd'Old and Max = Max'Old)
   is
   begin
      if X > Max then
         Snd := Max;
         Max := X;
      elsif X < Max then
         Snd := X;
      end if;
   end Update;

   procedure Seen_One (X : Integer) is
   begin
      if X > Snd then
         Update (X);
      end if;
   end Seen_One;

   procedure Seen_Two (X, Y : Natural) is
   begin
      if X > Max then
         Max := Y;
         Snd := X;
      elsif X > Snd then
         Update (Y);
         Seen_One (X);
      else
         Seen_One (Y);
      end if;
   end Seen_Two;

end Functional_Proved;
