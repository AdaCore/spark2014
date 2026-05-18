procedure Main with SPARK_Mode is
   type R is record
      F : Integer;
   end record;

   type R_Pos is new R with Predicate => R_Pos.F > 0;

   X : R := (F => 0);
   Y : R_Pos renames R_Pos (X);
begin
   null;
end Main;
