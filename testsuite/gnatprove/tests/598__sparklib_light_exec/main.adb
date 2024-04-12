with SPARK.Containers.Functional.Sets;
procedure Main with SPARK_Mode is
   package Int_Sets is new SPARK.Containers.Functional.Sets (Integer);

   X : Int_Sets.Set with Ghost;
begin
   X := Int_Sets.Add (X, 1);
   X := Int_Sets.Add (X, 1);
end Main;
