with Through_Model; use Through_Model;

procedure Main with SPARK_Mode is
   L : constant List := [1, 2, 3, 4, 5, 6];
begin
   pragma Assert (My_Seqs.Get (Model (L), 4) = 4);
end Main;
