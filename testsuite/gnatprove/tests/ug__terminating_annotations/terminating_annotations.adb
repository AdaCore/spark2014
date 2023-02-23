package body Terminating_Annotations with SPARK_Mode is

   procedure P_Rec (X : Natural) is
   begin
      if X = 0 then
         return;
      else
         P_Rec (X - 1);
      end if;
   end P_Rec;

   procedure P_While (X : Natural) is
      Y : Natural := X;
   begin
      while Y > 0 loop
         Y := Y - 1;
      end loop;
   end P_While;

   procedure P_Not_SPARK (X : Natural) with SPARK_Mode => Off is
      Y : Natural := X;
   begin
      while Y > 0 loop
         Y := Y - 1;
      end loop;
   end P_Not_SPARK;

   procedure Not_SPARK (X : Natural) with SPARK_Mode => Off is
   begin
      null;
   end Not_SPARK;

   procedure P_Call (X : Natural) is
   begin
      Not_SPARK (X);
   end P_Call;

   procedure P_Term (X : Natural) is
      Y : Natural := X;
   begin
      P_Rec (Y);
      P_While (Y);
      P_Not_SPARK (Y);
      P_Call (Y);

      while Y > 0 loop
         pragma Loop_Variant (Decreases => Y);
         Y := Y - 1;
      end loop;

      if X = 0 then
         return;
      else
         P_Term (X - 1);
      end if;
   end P_Term;
end Terminating_Annotations;
