with System.Storage_Elements;

package body Functional_Imported with
  SPARK_Mode,
  Refined_State => (Max_And_Snd => (Max, Snd))
is
   Max : Natural := 0;  --  max value seen
   for Max'Address use System.Storage_Elements.To_Address (16#8000_0000#);

   Snd : Natural := 0;  --  second max value seen
   for Snd'Address use System.Storage_Elements.To_Address (16#8000_0004#);

   function Invariant return Boolean is
     (if Max = 0 then Snd = 0 else Snd < Max);

   function Max_Value_Seen return Integer is (Max);

   function Second_Max_Value_Seen return Integer is (Snd);

   procedure Update (X : Natural) with
     Import,
     Convention => C,
     Global => (In_Out => (Max, Snd)),
     Pre  => X > Snd and then      --  support of maintenance
             Invariant,            --  invariant checking
     Post => Invariant and then    --  invariant checking
             (if X > Max'Old then  --  complete functional
                Snd = Max'Old and Max = X
              elsif X < Max'Old then
                Snd = X and Max = Max'Old
              else
                Snd = Snd'Old and Max = Max'Old);

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

end Functional_Imported;
