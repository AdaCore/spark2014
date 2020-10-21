package body Terminating_Annotations with SPARK_Mode is

   function F_Rec (X : Natural) return Natural is
   begin
      if X = 0 then
         return 0;
      else
         return F_Rec (X - 1);
      end if;
   end F_Rec;

   function F_While (X : Natural) return Natural is
      Y : Natural := X;
   begin
      while Y > 0 loop
         Y := Y - 1;
      end loop;
      return Y;
   end F_While;

   function F_Not_SPARK (X : Natural) return Natural with SPARK_Mode => Off is
      Y : Natural := X;
   begin
      while Y > 0 loop
         Y := Y - 1;
      end loop;
      return Y;
   end F_Not_SPARK;

   procedure Not_SPARK (X : Natural) with SPARK_Mode => Off is
   begin
      null;
   end Not_SPARK;

   function F_Call (X : Natural) return Natural is
   begin
      Not_SPARK (X);
      return 0;
   end F_Call;

   function F_Term (X : Natural) return Natural is
      Y : Natural := X;
   begin
      Y := F_Rec (Y);
      Y := F_While (Y);
      Y := F_Not_SPARK (Y);
      Y := F_Call (Y);

      while Y > 0 loop
         pragma Loop_Variant (Decreases => Y);
         Y := Y - 1;
      end loop;
      return Y;
   end F_Term;
end Terminating_Annotations;
