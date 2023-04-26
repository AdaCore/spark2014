with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Maps;

procedure Main with SPARK_Mode is

   type Int_Acc is access constant Integer;
   function My_Eq (X, Y : Int_Acc) return Boolean is
     ((X = null) = (Y = null) and then (X = null or else X.all = Y.all));

   package My_Sets is new SPARK.Containers.Functional.Sets (Int_Acc, My_Eq);

   package My_Maps is new SPARK.Containers.Functional.Maps (Int_Acc, Integer, My_Eq);
begin
   null;
end Main;
