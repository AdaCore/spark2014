with Interval_Trees;
with Types;

procedure Populate_Tree(T : in out Interval_Trees.Tree; Data : in Types.Interval_Array_Type)
  with
    SPARK_Mode => On,
    Global     => null,
    Depends    => (T => (T, Data)) is
begin
   for I in Data'Range loop
      Interval_Trees.Insert(T, Data(I));
   end loop;
end Populate_Tree;
