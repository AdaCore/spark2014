package body Integrity_Proved with
  SPARK_Mode
is
   Max : Natural := 0;  --  max value seen
   Snd : Natural := 0;  --  second max value seen

   function Invariant return Boolean is (Snd <= Max);

   procedure Update (X : Natural) with
     Pre  => X > Snd and then  --  support of maintenance
             Invariant,        --  invariant checking
     Post => Invariant         --  invariant checking
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

end Integrity_Proved;
