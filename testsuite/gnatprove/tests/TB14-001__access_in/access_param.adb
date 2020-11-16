procedure Access_Param with SPARK_Mode Is
   type T is access Boolean;

   procedure Flip (X : T) with Import;

   function Create return T with Import;

   type R is record
      F : T;
   end record;

   X : constant R := (others => <>);
begin
   Flip (Create);
   Flip (X.F);
end Access_Param;
