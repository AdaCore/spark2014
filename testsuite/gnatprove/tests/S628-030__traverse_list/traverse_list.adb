procedure Traverse_List with SPARK_Mode is
    type List;
    type List_Acc is access List;
    type List is record
       Val  : Integer;
       Next : List_Acc;
    end record;

    function Get_Nth (X : access List; I : Natural) return access List is
       Res : access List := X;
    begin
       for J in 1 .. I loop
          exit when Res = null;
          Res := Res.Next;
       end loop;
       return Res;
    end Get_Nth;
begin
    null;
end Traverse_List;
